"""
This module houses the entire Makefile parsing and execution
engine.

It's all collapsed into one module because Make concepts are heavily
intertwined -- expansion requires parsing, parsing requires expansion,
execution requires parsing, etc, etc.
"""
from __future__ import print_function

import logging, re, os, sys, subprocess
from functools import reduce

import process, util, implicit
from pymake import errors
from pymake.globrelative import hasglob, glob

try:
    from cStringIO import StringIO
except ImportError:
    from io import StringIO

"""
A representation of makefile data structures.
"""
if sys.version_info[0] < 3:
    str_type = basestring
else:
    str_type = str

_data_log = logging.getLogger('pymake.data')

def withoutdups(it):
    r = set()
    for i in it:
        if not i in r:
            r.add(i)
            yield i

def mtimeislater(deptime, targettime):
    """
    Is the mtime of the dependency later than the target?
    """

    if deptime is None:
        return True
    if targettime is None:
        return False
    # int(1000*x) because of http://bugs.python.org/issue10148
    return int(1000 * deptime) > int(1000 * targettime)

def getmtime(path):
    try:
        s = os.stat(path)
        return s.st_mtime
    except OSError:
        return None

def stripdotslash(s):
    if s.startswith('./'):
        st = s[2:]
        return st if st != '' else '.'
    return s

def stripdotslashes(sl):
    for s in sl:
        yield stripdotslash(s)

def getindent(stack):
    return ''.ljust(len(stack) - 1)

def _if_else(c, t, f):
    if c:
        return t()
    return f()


class BaseExpansion(object):
    """Base class for expansions.

    A make expansion is the parsed representation of a string, which may
    contain references to other elements.
    """

    @property
    def is_static_string(self):
        """Returns whether the expansion is composed of static string content.

        This is always True for StringExpansion. It will be True for Expansion
        only if all elements of that Expansion are static strings.
        """
        raise Exception('Must be implemented in child class.')

    def functions(self, descend=False):
        """Obtain all functions inside this expansion.

        This is a generator for pymake.functions.Function instances.

        By default, this only returns functions existing as the primary
        elements of this expansion. If `descend` is True, it will descend into
        child expansions and extract all functions in the tree.
        """
        # An empty generator. Yeah, it's weird.
        for x in []:
            yield x

    def variable_references(self, descend=False):
        """Obtain all variable references in this expansion.

        This is a generator for pymake.functionsVariableRef instances.

        To retrieve the names of variables, simply query the `vname` field on
        the returned instances. Most of the time these will be StringExpansion
        instances.
        """
        for f in self.functions(descend=descend):
            if not isinstance(f, VariableRef):
                continue

            yield f

    @property
    def is_filesystem_dependent(self):
        """Whether this expansion may query the filesystem for evaluation.

        This effectively asks "is any function in this expansion dependent on
        the filesystem.
        """
        for f in self.functions(descend=True):
            if f.is_filesystem_dependent:
                return True

        return False

    @property
    def is_shell_dependent(self):
        """Whether this expansion may invoke a shell for evaluation."""

        for f in self.functions(descend=True):
            if isinstance(f, ShellFunction):
                return True

        return False


class StringExpansion(BaseExpansion):
    """An Expansion representing a static string.

    This essentially wraps a single str instance.
    """

    __slots__ = ('loc', 's',)
    simple = True

    def __init__(self, s, loc):
        assert isinstance(s, str_type)
        self.s = s
        self.loc = loc

    def lstrip(self):
        self.s = self.s.lstrip()

    def rstrip(self):
        self.s = self.s.rstrip()

    def isempty(self):
        return self.s == ''

    def resolve(self, i, j, fd, k=None):
        fd.write(self.s)

    def resolvestr(self, i, j, k=None):
        return self.s

    def resolvesplit(self, i, j, k=None):
        return self.s.split()

    def clone(self):
        e = Expansion(self.loc)
        e.appendstr(self.s)
        return e

    @property
    def is_static_string(self):
        return True

    def __len__(self):
        return 1

    def __getitem__(self, i):
        assert i == 0
        return self.s, False

    def __repr__(self):
        return "Exp<%s>(%r)" % (self.loc, self.s)

    def __eq__(self, other):
        """We only compare the string contents."""
        return self.s == other

    def __ne__(self, other):
        return not self.__eq__(other)

    def to_source(self, escape_variables=False, escape_comments=False):
        s = self.s

        if escape_comments:
            s = s.replace('#', '\\#')

        if escape_variables:
            return s.replace('$', '$$')

        return s


class Expansion(BaseExpansion, list):
    """A representation of expanded data.

    This is effectively an ordered list of StringExpansion and
    pymake.function.Function instances. Every item in the collection appears in
    the same context in a make file.
    """

    __slots__ = ('loc',)
    simple = False

    def __init__(self, loc=None):
        # A list of (element, isfunc) tuples
        # element is either a string or a function
        self.loc = loc

    @staticmethod
    def fromstring(s, path):
        return StringExpansion(s, Location(path, 1, 0))

    def clone(self):
        e = Expansion()
        e.extend(self)
        return e

    def appendstr(self, s):
        assert isinstance(s, str_type)
        if s == '':
            return

        self.append((s, False))

    def appendfunc(self, func):
        assert isinstance(func, Function)
        self.append((func, True))

    def concat(self, o):
        """Concatenate the other expansion on to this one."""
        if o.simple:
            self.appendstr(o.s)
        else:
            self.extend(o)

    def isempty(self):
        return (not len(self)) or self[0] == ('', False)

    def lstrip(self):
        """Strip leading literal whitespace from this expansion."""
        while True:
            i, isfunc = self[0]
            if isfunc:
                return

            i = i.lstrip()
            if i != '':
                self[0] = i, False
                return

            del self[0]

    def rstrip(self):
        """Strip trailing literal whitespace from this expansion."""
        while True:
            i, isfunc = self[-1]
            if isfunc:
                return

            i = i.rstrip()
            if i != '':
                self[-1] = i, False
                return

            del self[-1]

    def finish(self):
        # Merge any adjacent literal strings:
        strings = []
        elements = []
        for (e, isfunc) in self:
            if isfunc:
                if strings:
                    s = ''.join(strings)
                    if s:
                        elements.append((s, False))
                    strings = []
                elements.append((e, True))
            else:
                strings.append(e)

        if not elements:
            # This can only happen if there were no function elements.
            return StringExpansion(''.join(strings), self.loc)

        if strings:
            s = ''.join(strings)
            if s:
                elements.append((s, False))

        if len(elements) < len(self):
            self[:] = elements

        return self

    def resolve(self, makefile, variables, fd, setting=[]):
        """
        Resolve this variable into a value, by interpolating the value
        of other variables.

        @param setting (Variable instance) the variable currently
               being set, if any. Setting variables must avoid self-referential
               loops.
        """
        assert isinstance(makefile, Makefile)
        assert isinstance(variables, Variables)
        assert isinstance(setting, list)

        for e, isfunc in self:
            if isfunc:
                e.resolve(makefile, variables, fd, setting)
            else:
                assert isinstance(e, str_type)
                fd.write(e)

    def resolvestr(self, makefile, variables, setting=[]):
        fd = StringIO()
        self.resolve(makefile, variables, fd, setting)
        return fd.getvalue()

    def resolvesplit(self, makefile, variables, setting=[]):
        return self.resolvestr(makefile, variables, setting).split()

    @property
    def is_static_string(self):
        """An Expansion is static if all its components are strings, not
        functions."""
        for e, is_func in self:
            if is_func:
                return False

        return True

    def functions(self, descend=False):
        for e, is_func in self:
            if is_func:
                yield e

            if descend:
                for exp in e.expansions(descend=True):
                    for f in exp.functions(descend=True):
                        yield f

    def __repr__(self):
        return "<Expansion with elements: %r>" % ([e for e, isfunc in self],)

    def to_source(self, escape_variables=False, escape_comments=False):
        parts = []
        for e, is_func in self:
            if is_func:
                parts.append(e.to_source())
                continue

            if escape_variables:
                parts.append(e.replace('$', '$$'))
                continue

            parts.append(e)

        return ''.join(parts)

    def __eq__(self, other):
        if not isinstance(other, (Expansion, StringExpansion)):
            return False

        # Expansions are equivalent if adjacent string literals normalize to
        # the same value. So, we must normalize before any comparisons are
        # made.
        a = self.clone().finish()

        if isinstance(other, StringExpansion):
            if isinstance(a, StringExpansion):
                return a == other

            # A normalized Expansion != StringExpansion.
            return False

        b = other.clone().finish()

        # b could be a StringExpansion now.
        if isinstance(b, StringExpansion):
            if isinstance(a, StringExpansion):
                return a == b

            # Our normalized Expansion != normalized StringExpansion.
            return False

        if len(a) != len(b):
            return False

        for i in range(len(self)):
            e1, is_func1 = a[i]
            e2, is_func2 = b[i]

            if is_func1 != is_func2:
                return False

            if type(e1) != type(e2):
                return False

            if e1 != e2:
                return False

        return True

    def __ne__(self, other):
        return not self.__eq__(other)

class Variables(object):
    """
    A mapping from variable names to variables. Variables have flavor, source, and value. The value is an 
    expansion object.
    """

    __slots__ = ('parent', '_map')

    FLAVOR_RECURSIVE = 0
    FLAVOR_SIMPLE = 1
    FLAVOR_APPEND = 2

    SOURCE_OVERRIDE = 0
    SOURCE_COMMANDLINE = 1
    SOURCE_MAKEFILE = 2
    SOURCE_ENVIRONMENT = 3
    SOURCE_AUTOMATIC = 4
    SOURCE_IMPLICIT = 5

    def __init__(self, parent=None):
        self._map = {} # vname -> flavor, source, valuestr, valueexp
        self.parent = parent

    def readfromenvironment(self, env):
        for k, v in env.items():
            self.set(k, self.FLAVOR_RECURSIVE, self.SOURCE_ENVIRONMENT, v)

    def get(self, name, expand=True):
        """
        Get the value of a named variable. Returns a tuple (flavor, source, value)

        If the variable is not present, returns (None, None, None)

        @param expand If true, the value will be returned as an expansion. If false,
        it will be returned as an unexpanded string.
        """
        flavor, source, valuestr, valueexp = self._map.get(name, (None, None, None, None))
        if flavor is not None:
            if expand and flavor != self.FLAVOR_SIMPLE and valueexp is None:
                d = Data.fromstring(valuestr, Location("Expansion of variables '%s'" % (name,), 1, 0))
                valueexp, t, o = parsemakesyntax(d, 0, (), iterdata)
                self._map[name] = flavor, source, valuestr, valueexp

            if flavor == self.FLAVOR_APPEND:
                if self.parent:
                    pflavor, psource, pvalue = self.parent.get(name, expand)
                else:
                    pflavor, psource, pvalue = None, None, None

                if pvalue is None:
                    flavor = self.FLAVOR_RECURSIVE
                    # fall through
                else:
                    if source > psource:
                        # TODO: log a warning?
                        return pflavor, psource, pvalue

                    if not expand:
                        return pflavor, psource, pvalue + ' ' + valuestr

                    pvalue = pvalue.clone()
                    pvalue.appendstr(' ')
                    pvalue.concat(valueexp)

                    return pflavor, psource, pvalue
                    
            if not expand:
                return flavor, source, valuestr

            if flavor == self.FLAVOR_RECURSIVE:
                val = valueexp
            else:
                val = Expansion.fromstring(valuestr, "Expansion of variable '%s'" % (name,))

            return flavor, source, val

        if self.parent is not None:
            return self.parent.get(name, expand)

        return (None, None, None)

    def set(self, name, flavor, source, value, force=False):
        assert flavor in (self.FLAVOR_RECURSIVE, self.FLAVOR_SIMPLE)
        assert source in (self.SOURCE_OVERRIDE, self.SOURCE_COMMANDLINE, self.SOURCE_MAKEFILE, self.SOURCE_ENVIRONMENT, self.SOURCE_AUTOMATIC, self.SOURCE_IMPLICIT)
        assert isinstance(value, str_type), "expected str, got %s" % type(value)

        prevflavor, prevsource, prevvalue = self.get(name)
        if prevsource is not None and source > prevsource and not force:
            # TODO: give a location for this warning
            _data_log.info("not setting variable '%s', set by higher-priority source to value '%s'" % (name, prevvalue))
            return

        self._map[name] = flavor, source, value, None

    def append(self, name, source, value, variables, makefile):
        assert source in (self.SOURCE_OVERRIDE, self.SOURCE_MAKEFILE, self.SOURCE_AUTOMATIC)
        assert isinstance(value, str_type)

        if name not in self._map:
            self._map[name] = self.FLAVOR_APPEND, source, value, None
            return

        prevflavor, prevsource, prevvalue, valueexp = self._map[name]
        if source > prevsource:
            # TODO: log a warning?
            return

        if prevflavor == self.FLAVOR_SIMPLE:
            d = Data.fromstring(value, Location("Expansion of variables '%s'" % (name,), 1, 0))
            valueexp, t, o = parsemakesyntax(d, 0, (), iterdata)

            val = valueexp.resolvestr(makefile, variables, [name])
            self._map[name] = prevflavor, prevsource, prevvalue + ' ' + val, None
            return

        newvalue = prevvalue + ' ' + value
        self._map[name] = prevflavor, prevsource, newvalue, None

    def merge(self, other):
        assert isinstance(other, Variables)
        for k, flavor, source, value in other:
            self.set(k, flavor, source, value)

    def __iter__(self):
        for k, (flavor, source, value, valueexp) in self._map.items():
            yield k, flavor, source, value

    def __contains__(self, item):
        return item in self._map

class Pattern(object):
    """
    A pattern is a string, possibly with a % substitution character. From the GNU make manual:

    '%' characters in pattern rules can be quoted with precending backslashes ('\'). Backslashes that
    would otherwise quote '%' charcters can be quoted with more backslashes. Backslashes that
    quote '%' characters or other backslashes are removed from the pattern before it is compared t
    file names or has a stem substituted into it. Backslashes that are not in danger of quoting '%'
    characters go unmolested. For example, the pattern the\%weird\\%pattern\\ has `the%weird\' preceding
    the operative '%' character, and 'pattern\\' following it. The final two backslashes are left alone
    because they cannot affect any '%' character.

    This insane behavior probably doesn't matter, but we're compatible just for shits and giggles.
    """

    __slots__ = ('data')

    def __init__(self, s):
        r = []
        i = 0
        slen = len(s)
        while i < slen:
            c = s[i]
            if c == '\\':
                nc = s[i + 1]
                if nc == '%':
                    r.append('%')
                    i += 1
                elif nc == '\\':
                    r.append('\\')
                    i += 1
                else:
                    r.append(c)
            elif c == '%':
                self.data = (''.join(r), s[i+1:])
                return
            else:
                r.append(c)
            i += 1

        # This is different than (s,) because \% and \\ have been unescaped. Parsing patterns is
        # context-sensitive!
        self.data = (''.join(r),)

    def ismatchany(self):
        return self.data == ('','')

    def ispattern(self):
        return len(self.data) == 2

    def __hash__(self):
        return self.data.__hash__()

    def __eq__(self, o):
        assert isinstance(o, Pattern)
        return self.data == o.data

    def gettarget(self):
        assert not self.ispattern()
        return self.data[0]

    def hasslash(self):
        return self.data[0].find('/') != -1 or self.data[1].find('/') != -1

    def match(self, word):
        """
        Match this search pattern against a word (string).

        @returns None if the word doesn't match, or the matching stem.
                      If this is a %-less pattern, the stem will always be ''
        """
        d = self.data
        if len(d) == 1:
            if word == d[0]:
                return word
            return None

        d0, d1 = d
        l1 = len(d0)
        l2 = len(d1)
        if len(word) >= l1 + l2 and word.startswith(d0) and word.endswith(d1):
            if l2 == 0:
                return word[l1:]
            return word[l1:-l2]

        return None

    def resolve(self, dir, stem):
        if self.ispattern():
            return dir + self.data[0] + stem + self.data[1]

        return self.data[0]

    def subst(self, replacement, word, mustmatch):
        """
        Given a word, replace the current pattern with the replacement pattern, a la 'patsubst'

        @param mustmatch If true and this pattern doesn't match the word, throw a DataError. Otherwise
                         return word unchanged.
        """
        assert isinstance(replacement, str_type)

        stem = self.match(word)
        if stem is None:
            if mustmatch:
                raise errors.DataError("target '%s' doesn't match pattern" % (word,))
            return word

        if not self.ispattern():
            # if we're not a pattern, the replacement is not parsed as a pattern either
            return replacement

        return Pattern(replacement).resolve('', stem)

    def __repr__(self):
        return "<Pattern with data %r>" % (self.data,)

    _backre = re.compile(r'[%\\]')
    def __str__(self):
        if not self.ispattern():
            return self._backre.sub(r'\\\1', self.data[0])

        return self._backre.sub(r'\\\1', self.data[0]) + '%' + self.data[1]

class RemakeTargetSerially(object):
    __slots__ = ('target', 'makefile', 'indent', 'rlist')

    def __init__(self, target, makefile, indent, rlist):
        self.target = target
        self.makefile = makefile
        self.indent = indent
        self.rlist = rlist
        self.commandscb(False)

    def resolvecb(self, error, didanything):
        assert error in (True, False)

        if didanything:
            self.target.didanything = True

        if error:
            self.target.error = True
            self.makefile.error = True
            if not self.makefile.keepgoing:
                self.target.notifydone(self.makefile)
                return
            else:
                # don't run the commands!
                del self.rlist[0]
                self.commandscb(error=False)
        else:
            self.rlist.pop(0).runcommands(self.indent, self.commandscb)

    def commandscb(self, error):
        assert error in (True, False)

        if error:
            self.target.error = True
            self.makefile.error = True

        if self.target.error and not self.makefile.keepgoing:
            self.target.notifydone(self.makefile)
            return

        if not len(self.rlist):
            self.target.notifydone(self.makefile)
        else:
            self.rlist[0].resolvedeps(True, self.resolvecb)

class RemakeTargetParallel(object):
    __slots__ = ('target', 'makefile', 'indent', 'rlist', 'rulesremaining', 'currunning')

    def __init__(self, target, makefile, indent, rlist):
        self.target = target
        self.makefile = makefile
        self.indent = indent
        self.rlist = rlist

        self.rulesremaining = len(rlist)
        self.currunning = False

        for r in rlist:
            makefile.context.defer(self.doresolve, r)

    def doresolve(self, r):
        if self.makefile.error and not self.makefile.keepgoing:
            r.error = True
            self.resolvecb(True, False)
        else:
            r.resolvedeps(False, self.resolvecb)

    def resolvecb(self, error, didanything):
        assert error in (True, False)

        if error:
            self.target.error = True

        if didanything:
            self.target.didanything = True

        self.rulesremaining -= 1

        # commandscb takes care of the details if we're currently building
        # something
        if self.currunning:
            return

        self.runnext()

    def runnext(self):
        assert not self.currunning

        if self.makefile.error and not self.makefile.keepgoing:
            self.rlist = []
        else:
            while len(self.rlist) and self.rlist[0].error:
                del self.rlist[0]

        if not len(self.rlist):
            if not self.rulesremaining:
                self.target.notifydone(self.makefile)
            return

        if self.rlist[0].depsremaining != 0:
            return

        self.currunning = True
        rule = self.rlist.pop(0)
        self.makefile.context.defer(rule.runcommands, self.indent, self.commandscb)

    def commandscb(self, error):
        assert error in (True, False)
        if error:
            self.target.error = True
            self.makefile.error = True

        assert self.currunning
        self.currunning = False
        self.runnext()

class RemakeRuleContext(object):
    def __init__(self, target, makefile, rule, deps,
                 targetstack, avoidremakeloop):
        self.target = target
        self.makefile = makefile
        self.rule = rule
        self.deps = deps
        self.targetstack = targetstack
        self.avoidremakeloop = avoidremakeloop

        self.running = False
        self.error = False
        self.depsremaining = len(deps) + 1
        self.remake = False

    def resolvedeps(self, serial, cb):
        self.resolvecb = cb
        self.didanything = False
        if serial:
            self._resolvedepsserial()
        else:
            self._resolvedepsparallel()

    def _weakdepfinishedserial(self, error, didanything):
        if error:
            self.remake = True
        self._depfinishedserial(False, didanything)

    def _depfinishedserial(self, error, didanything):
        assert error in (True, False)

        if didanything:
            self.didanything = True

        if error:
            self.error = True
            if not self.makefile.keepgoing:
                self.resolvecb(error=True, didanything=self.didanything)
                return
        
        if len(self.resolvelist):
            dep, weak = self.resolvelist.pop(0)
            self.makefile.context.defer(dep.make,
                                        self.makefile, self.targetstack, weak and self._weakdepfinishedserial or self._depfinishedserial)
        else:
            self.resolvecb(error=self.error, didanything=self.didanything)

    def _resolvedepsserial(self):
        self.resolvelist = list(self.deps)
        self._depfinishedserial(False, False)

    def _startdepparallel(self, d):
        dep, weak = d
        if weak:
            depfinished = self._weakdepfinishedparallel
        else:
            depfinished = self._depfinishedparallel
        if self.makefile.error:
            depfinished(True, False)
        else:
            dep.make(self.makefile, self.targetstack, depfinished)

    def _weakdepfinishedparallel(self, error, didanything):
        if error:
            self.remake = True
        self._depfinishedparallel(False, didanything)

    def _depfinishedparallel(self, error, didanything):
        assert error in (True, False)

        if error:
            print("<%s>: Found error" % self.target.target)
            self.error = True
        if didanything:
            self.didanything = True

        self.depsremaining -= 1
        if self.depsremaining == 0:
            self.resolvecb(error=self.error, didanything=self.didanything)

    def _resolvedepsparallel(self):
        self.depsremaining -= 1
        if self.depsremaining == 0:
            self.resolvecb(error=self.error, didanything=self.didanything)
            return

        self.didanything = False

        for d in self.deps:
            self.makefile.context.defer(self._startdepparallel, d)

    def _commandcb(self, error):
        assert error in (True, False)

        if error:
            self.runcb(error=True)
            return

        if len(self.commands):
            self.commands.pop(0)(self._commandcb)
        else:
            self.runcb(error=False)

    def runcommands(self, indent, cb):
        assert not self.running
        self.running = True

        self.runcb = cb

        if self.rule is None or not len(self.rule.commands):
            if self.target.mtime is None:
                self.target.beingremade()
            else:
                for d, weak in self.deps:
                    if mtimeislater(d.mtime, self.target.mtime):
                        if d.mtime is None:
                            self.target.beingremade()
                        else:
                            _data_log.info("%sNot remaking %s ubecause it would have no effect, even though %s is newer.", indent, self.target.target, d.target)
                        break
            cb(error=False)
            return

        if self.rule.doublecolon:
            if len(self.deps) == 0:
                if self.avoidremakeloop:
                    _data_log.info("%sNot remaking %s using rule at %s because it would introduce an infinite loop.", indent, self.target.target, self.rule.loc)
                    cb(error=False)
                    return

        remake = self.remake
        if remake:
            _data_log.info("%sRemaking %s using rule at %s: weak dependency was not found.", indent, self.target.target, self.rule.loc)
        else:
            if self.target.mtime is None:
                remake = True
                _data_log.info("%sRemaking %s using rule at %s: target doesn't exist or is a forced target", indent, self.target.target, self.rule.loc)

        if not remake:
            if self.rule.doublecolon:
                if len(self.deps) == 0:
                    _data_log.info("%sRemaking %s using rule at %s because there are no prerequisites listed for a double-colon rule.", indent, self.target.target, self.rule.loc)
                    remake = True

        if not remake:
            for d, weak in self.deps:
                if mtimeislater(d.mtime, self.target.mtime):
                    _data_log.info("%sRemaking %s using rule at %s because %s is newer.", indent, self.target.target, self.rule.loc, d.target)
                    remake = True
                    break

        if remake:
            self.target.beingremade()
            self.target.didanything = True
            try:
                self.commands = [c for c in self.rule.getcommands(self.target, self.makefile)]
            except errors.MakeError as e:
                print(e)
                sys.stdout.flush()
                cb(error=True)
                return

            self._commandcb(False)
        else:
            cb(error=False)

MAKESTATE_NONE = 0
MAKESTATE_FINISHED = 1
MAKESTATE_WORKING = 2

class Target(object):
    """
    An actual (non-pattern) target.

    It holds target-specific variables and a list of rules. It may also point to a parent
    PatternTarget, if this target is being created by an implicit rule.

    The rules associated with this target may be Rule instances or, in the case of static pattern
    rules, PatternRule instances.
    """

    wasremade = False

    def __init__(self, target, makefile):
        assert isinstance(target, str_type)
        self.target = target
        self.vpathtarget = None
        self.rules = []
        self.variables = Variables(makefile.variables)
        self.explicit = False
        self._state = MAKESTATE_NONE

    def addrule(self, rule):
        assert isinstance(rule, (Rule, PatternRuleInstance))
        if len(self.rules) and rule.doublecolon != self.rules[0].doublecolon:
            raise errors.DataError("Cannot have single- and double-colon rules for the same target. Prior rule location: %s" % self.rules[0].loc, rule.loc)

        if isinstance(rule, PatternRuleInstance):
            if len(rule.prule.targetpatterns) != 1:
                raise errors.DataError("Static pattern rules must only have one target pattern", rule.prule.loc)
            if rule.prule.targetpatterns[0].match(self.target) is None:
                raise errors.DataError("Static pattern rule doesn't match target '%s'" % self.target, rule.loc)

        self.rules.append(rule)

    def isdoublecolon(self):
        return self.rules[0].doublecolon

    def isphony(self, makefile):
        """Is this a phony target? We don't check for existence of phony targets."""
        return makefile.gettarget('.PHONY').hasdependency(self.target)

    def hasdependency(self, t):
        for rule in self.rules:
            if t in rule.prerequisites:
                return True

        return False

    def resolveimplicitrule(self, makefile, targetstack, rulestack):
        """
        Try to resolve an implicit rule to build this target.
        """
        # The steps in the GNU make manual Implicit-Rule-Search.html are very detailed. I hope they can be trusted.

        indent = getindent(targetstack)

        _data_log.info("%sSearching for implicit rule to make '%s'", indent, self.target)

        dir, s, file = util.strrpartition(self.target, '/')
        dir = dir + s

        candidates = [] # list of PatternRuleInstance

        hasmatch = util.any((r.hasspecificmatch(file) for r in makefile.implicitrules))

        for r in makefile.implicitrules:
            if r in rulestack:
                _data_log.info("%s %s: Avoiding implicit rule recursion", indent, r.loc)
                continue

            if not len(r.commands):
                continue

            for ri in r.matchesfor(dir, file, hasmatch):
                candidates.append(ri)
            
        newcandidates = []

        for r in candidates:
            depfailed = None
            for p in r.prerequisites:
                t = makefile.gettarget(p)
                t.resolvevpath(makefile)
                if not t.explicit and t.mtime is None:
                    depfailed = p
                    break

            if depfailed is not None:
                if r.doublecolon:
                    _data_log.info("%s Terminal rule at %s doesn't match: prerequisite '%s' not mentioned and doesn't exist.", indent, r.loc, depfailed)
                else:
                    newcandidates.append(r)
                continue

            _data_log.info("%sFound implicit rule at %s for target '%s'", indent, r.loc, self.target)
            self.rules.append(r)
            return

        # Try again, but this time with chaining and without terminal (double-colon) rules

        for r in newcandidates:
            newrulestack = rulestack + [r.prule]

            depfailed = None
            for p in r.prerequisites:
                t = makefile.gettarget(p)
                try:
                    t.resolvedeps(makefile, targetstack, newrulestack, True)
                except errors.ResolutionError:
                    depfailed = p
                    break

            if depfailed is not None:
                _data_log.info("%s Rule at %s doesn't match: prerequisite '%s' could not be made.", indent, r.loc, depfailed)
                continue

            _data_log.info("%sFound implicit rule at %s for target '%s'", indent, r.loc, self.target)
            self.rules.append(r)
            return

        _data_log.info("%sCouldn't find implicit rule to remake '%s'", indent, self.target)

    def ruleswithcommands(self):
        "The number of rules with commands"
        return reduce(lambda i, rule: i + (len(rule.commands) > 0), self.rules, 0)

    def resolvedeps(self, makefile, targetstack, rulestack, recursive):
        """
        Resolve the actual path of this target, using vpath if necessary.

        Recursively resolve dependencies of this target. This means finding implicit
        rules which match the target, if appropriate.

        Figure out whether this target needs to be rebuild, and set self.outofdate
        appropriately.

        @param targetstack is the current stack of dependencies being resolved. If
               this target is already in targetstack, bail to prevent infinite
               recursion.
        @param rulestack is the current stack of implicit rules being used to resolve
               dependencies. A rule chain cannot use the same implicit rule twice.
        """
        assert makefile.parsingfinished

        if self.target in targetstack:
            raise errors.ResolutionError("Recursive dependency: %s -> %s" % (
                    " -> ".join(targetstack), self.target))

        targetstack = targetstack + [self.target]
        
        indent = getindent(targetstack)

        _data_log.info("%sConsidering target '%s'", indent, self.target)

        self.resolvevpath(makefile)

        # Sanity-check our rules. If we're single-colon, only one rule should have commands
        ruleswithcommands = self.ruleswithcommands()
        if len(self.rules) and not self.isdoublecolon():
            if ruleswithcommands > 1:
                # In GNU make this is a warning, not an error. I'm going to be stricter.
                # TODO: provide locations
                raise errors.DataError("Target '%s' has multiple rules with commands." % self.target)

        if ruleswithcommands == 0:
            self.resolveimplicitrule(makefile, targetstack, rulestack)

        # If a target is mentioned, but doesn't exist, has no commands and no
        # prerequisites, it is special and exists just to say that targets which
        # depend on it are always out of date. This is like .FORCE but more
        # compatible with other makes.
        # Otherwise, we don't know how to make it.
        if not len(self.rules) and self.mtime is None and not util.any((len(rule.prerequisites) > 0
                                                                        for rule in self.rules)):
            raise errors.ResolutionError("No rule to make target '%s' needed by %r" % (self.target,
                                                                                targetstack))

        if recursive:
            for r in self.rules:
                newrulestack = rulestack + [r]
                for d in r.prerequisites:
                    dt = makefile.gettarget(d)
                    if dt.explicit:
                        continue

                    dt.resolvedeps(makefile, targetstack, newrulestack, True)

        for v in makefile.getpatternvariablesfor(self.target):
            self.variables.merge(v)

    def resolvevpath(self, makefile):
        if self.vpathtarget is not None:
            return

        if self.isphony(makefile):
            self.vpathtarget = self.target
            self.mtime = None
            return

        if self.target.startswith('-l'):
            stem = self.target[2:]
            f, s, e = makefile.variables.get('.LIBPATTERNS')
            if e is not None:
                libpatterns = [Pattern(stripdotslash(s)) for s in e.resolvesplit(makefile, makefile.variables)]
                if len(libpatterns):
                    searchdirs = ['']
                    searchdirs.extend(makefile.getvpath(self.target))

                    for lp in libpatterns:
                        if not lp.ispattern():
                            raise errors.DataError('.LIBPATTERNS contains a non-pattern')

                        libname = lp.resolve('', stem)

                        for dir in searchdirs:
                            libpath = util.normaljoin(dir, libname).replace('\\', '/')
                            fspath = util.normaljoin(makefile.workdir, libpath)
                            mtime = getmtime(fspath)
                            if mtime is not None:
                                self.vpathtarget = libpath
                                self.mtime = mtime
                                return

                    self.vpathtarget = self.target
                    self.mtime = None
                    return

        search = [self.target]
        if not os.path.isabs(self.target):
            search += [util.normaljoin(dir, self.target).replace('\\', '/')
                       for dir in makefile.getvpath(self.target)]

        targetandtime = self.searchinlocs(makefile, search)
        if targetandtime is not None:
            (self.vpathtarget, self.mtime) = targetandtime
            return

        self.vpathtarget = self.target
        self.mtime = None

    def searchinlocs(self, makefile, locs):
        """
        Look in the given locations relative to the makefile working directory
        for a file. Return a pair of the target and the mtime if found, None
        if not.
        """
        for t in locs:
            fspath = util.normaljoin(makefile.workdir, t).replace('\\', '/')
            mtime = getmtime(fspath)
#            _data_log.info("Searching %s ... checking %s ... mtime %r" % (t, fspath, mtime))
            if mtime is not None:
                return (t, mtime)

        return None
        
    def beingremade(self):
        """
        When we remake ourself, we have to drop any vpath prefixes.
        """
        self.vpathtarget = self.target
        self.wasremade = True

    def notifydone(self, makefile):
        assert self._state == MAKESTATE_WORKING, "State was %s" % self._state
        # If we were remade then resolve mtime again
        if self.wasremade:
            targetandtime = self.searchinlocs(makefile, [self.target])
            if targetandtime is not None:
                (_, self.mtime) = targetandtime
            else:
                self.mtime = None

        self._state = MAKESTATE_FINISHED
        for cb in self._callbacks:
            makefile.context.defer(cb, error=self.error, didanything=self.didanything)
        del self._callbacks 

    def make(self, makefile, targetstack, cb, avoidremakeloop=False, printerror=True):
        """
        If we are out of date, asynchronously make ourself. This is a multi-stage process, mostly handled
        by the helper objects RemakeTargetSerially, RemakeTargetParallel,
        RemakeRuleContext. These helper objects should keep us from developing
        any cyclical dependencies.

        * resolve dependencies (synchronous)
        * gather a list of rules to execute and related dependencies (synchronous)
        * for each rule (in parallel)
        ** remake dependencies (asynchronous)
        ** build list of commands to execute (synchronous)
        ** execute each command (asynchronous)
        * asynchronously notify when all rules are complete

        @param cb A callback function to notify when remaking is finished. It is called
               thusly: callback(error=True/False, didanything=True/False)
               If there is no asynchronous activity to perform, the callback may be called directly.
        """

        serial = makefile.context.jcount == 1
        
        if self._state == MAKESTATE_FINISHED:
            cb(error=self.error, didanything=self.didanything)
            return
            
        if self._state == MAKESTATE_WORKING:
            assert not serial
            self._callbacks.append(cb)
            return

        assert self._state == MAKESTATE_NONE

        self._state = MAKESTATE_WORKING
        self._callbacks = [cb]
        self.error = False
        self.didanything = False

        indent = getindent(targetstack)

        try:
            self.resolvedeps(makefile, targetstack, [], False)
        except errors.MakeError as e:
            if printerror:
                print(e)
            self.error = True
            self.notifydone(makefile)
            return

        assert self.vpathtarget is not None, "Target was never resolved!"
        if not len(self.rules):
            self.notifydone(makefile)
            return

        if self.isdoublecolon():
            rulelist = [RemakeRuleContext(self, makefile, r, [(makefile.gettarget(p), False) for p in r.prerequisites], targetstack, avoidremakeloop) for r in self.rules]
        else:
            alldeps = []

            commandrule = None
            for r in self.rules:
                rdeps = [(makefile.gettarget(p), r.weakdeps) for p in r.prerequisites]
                if len(r.commands):
                    assert commandrule is None
                    commandrule = r
                    # The dependencies of the command rule are resolved before other dependencies,
                    # no matter the ordering of the other no-command rules
                    alldeps[0:0] = rdeps
                else:
                    alldeps.extend(rdeps)

            rulelist = [RemakeRuleContext(self, makefile, commandrule, alldeps, targetstack, avoidremakeloop)]

        targetstack = targetstack + [self.target]

        if serial:
            RemakeTargetSerially(self, makefile, indent, rulelist)
        else:
            RemakeTargetParallel(self, makefile, indent, rulelist)

def dirpart(p):
    d, s, f = util.strrpartition(p, '/')
    if d == '':
        return '.'

    return d

def filepart(p):
    d, s, f = util.strrpartition(p, '/')
    return f

def setautomatic(v, name, plist):
    v.set(name, Variables.FLAVOR_SIMPLE, Variables.SOURCE_AUTOMATIC, ' '.join(plist))
    v.set(name + 'D', Variables.FLAVOR_SIMPLE, Variables.SOURCE_AUTOMATIC, ' '.join((dirpart(p) for p in plist)))
    v.set(name + 'F', Variables.FLAVOR_SIMPLE, Variables.SOURCE_AUTOMATIC, ' '.join((filepart(p) for p in plist)))

def setautomaticvariables(v, makefile, target, prerequisites):
    prtargets = [makefile.gettarget(p) for p in prerequisites]
    prall = [pt.vpathtarget for pt in prtargets]
    proutofdate = [pt.vpathtarget for pt in withoutdups(prtargets)
                   if target.mtime is None or mtimeislater(pt.mtime, target.mtime)]
    
    setautomatic(v, '@', [target.vpathtarget])
    if len(prall):
        setautomatic(v, '<', [prall[0]])

    setautomatic(v, '?', proutofdate)
    setautomatic(v, '^', list(withoutdups(prall)))
    setautomatic(v, '+', prall)

def splitcommand(command):
    """
    Using the esoteric rules, split command lines by unescaped newlines.
    """
    start = 0
    i = 0
    while i < len(command):
        c = command[i]
        if c == '\\':
            i += 1
        elif c == '\n':
            yield command[start:i]
            i += 1
            start = i
            continue

        i += 1

    if i > start:
        yield command[start:i]

def findmodifiers(command):
    """
    Find any of +-@% prefixed on the command.
    @returns (command, isHidden, isRecursive, ignoreErrors, isNative)
    """

    isHidden = False
    isRecursive = False
    ignoreErrors = False
    isNative = False

    realcommand = command.lstrip(' \t\n@+-%')
    modset = set(command[:-len(realcommand)])
    return realcommand, '@' in modset, '+' in modset, '-' in modset, '%' in modset

class _CommandWrapper(object):
    def __init__(self, cline, ignoreErrors, loc, context, **kwargs):
        self.ignoreErrors = ignoreErrors
        self.loc = loc
        self.cline = cline
        self.kwargs = kwargs
        self.context = context

    def _cb(self, res):
        if res != 0 and not self.ignoreErrors:
            print("%s: command '%s' failed, return code %i" % (self.loc, self.cline, res))
            self.usercb(error=True)
        else:
            self.usercb(error=False)

    def __call__(self, cb):
        self.usercb = cb
        process.call(self.cline, loc=self.loc, cb=self._cb, context=self.context, **self.kwargs)

class _NativeWrapper(_CommandWrapper):
    def __init__(self, cline, ignoreErrors, loc, context,
                 pycommandpath, **kwargs):
        _CommandWrapper.__init__(self, cline, ignoreErrors, loc, context,
                                 **kwargs)
        if pycommandpath:
            self.pycommandpath = re.split('[%s\s]+' % os.pathsep,
                                          pycommandpath)
        else:
            self.pycommandpath = None

    def __call__(self, cb):
        # get the module and method to call
        parts, badchar = process.clinetoargv(self.cline, self.kwargs['cwd'])
        if parts is None:
            raise errors.DataError("native command '%s': shell metacharacter '%s' in command line" % (self.cline, badchar), self.loc)
        if len(parts) < 2:
            raise errors.DataError("native command '%s': no method name specified" % self.cline, self.loc)
        module = parts[0]
        method = parts[1]
        cline_list = parts[2:]
        self.usercb = cb
        process.call_native(module, method, cline_list,
                            loc=self.loc, cb=self._cb, context=self.context,
                            pycommandpath=self.pycommandpath, **self.kwargs)

def getcommandsforrule(rule, target, makefile, prerequisites, stem):
    v = Variables(parent=target.variables)
    setautomaticvariables(v, makefile, target, prerequisites)
    if stem is not None:
        setautomatic(v, '*', [stem])

    env = makefile.getsubenvironment(v)

    for c in rule.commands:
        cstring = c.resolvestr(makefile, v)
        for cline in splitcommand(cstring):
            cline, isHidden, isRecursive, ignoreErrors, isNative = findmodifiers(cline)
            if (isHidden or makefile.silent) and not makefile.justprint:
                echo = None
            else:
                echo = "%s$ %s" % (c.loc, cline)
            if not isNative:
                yield _CommandWrapper(cline, ignoreErrors=ignoreErrors, env=env, cwd=makefile.workdir, loc=c.loc, context=makefile.context,
                                      echo=echo, justprint=makefile.justprint)
            else:
                f, s, e = v.get("PYCOMMANDPATH", True)
                if e:
                    e = e.resolvestr(makefile, v, ["PYCOMMANDPATH"])
                yield _NativeWrapper(cline, ignoreErrors=ignoreErrors,
                                     env=env, cwd=makefile.workdir,
                                     loc=c.loc, context=makefile.context,
                                     echo=echo, justprint=makefile.justprint,
                                     pycommandpath=e)

class Rule(object):
    """
    A rule contains a list of prerequisites and a list of commands. It may also
    contain rule-specific variables. This rule may be associated with multiple targets.
    """

    def __init__(self, prereqs, doublecolon, loc, weakdeps):
        self.prerequisites = prereqs
        self.doublecolon = doublecolon
        self.commands = []
        self.loc = loc
        self.weakdeps = weakdeps

    def addcommand(self, c):
        assert isinstance(c, (Expansion, StringExpansion))
        self.commands.append(c)

    def getcommands(self, target, makefile):
        assert isinstance(target, Target)
        # Prerequisites are merged if the target contains multiple rules and is
        # not a terminal (double colon) rule. See
        # https://www.gnu.org/software/make/manual/make.html#Multiple-Targets.
        prereqs = []
        prereqs.extend(self.prerequisites)

        if not self.doublecolon:
            for rule in target.rules:
                # The current rule comes first, which is already in prereqs so
                # we don't need to add it again.
                if rule != self:
                    prereqs.extend(rule.prerequisites)

        return getcommandsforrule(self, target, makefile, prereqs, stem=None)
        # TODO: $* in non-pattern rules?

class PatternRuleInstance(object):
    weakdeps = False

    """
    A pattern rule instantiated for a particular target. It has the same API as Rule, but
    different internals, forwarding most information on to the PatternRule.
    """
    def __init__(self, prule, dir, stem, ismatchany):
        assert isinstance(prule, PatternRule)

        self.dir = dir
        self.stem = stem
        self.prule = prule
        self.prerequisites = prule.prerequisitesforstem(dir, stem)
        self.doublecolon = prule.doublecolon
        self.loc = prule.loc
        self.ismatchany = ismatchany
        self.commands = prule.commands

    def getcommands(self, target, makefile):
        assert isinstance(target, Target)
        return getcommandsforrule(self, target, makefile, self.prerequisites, stem=self.dir + self.stem)

    def __str__(self):
        return "Pattern rule at %s with stem '%s', matchany: %s doublecolon: %s" % (self.loc,
                                                                                    self.dir + self.stem,
                                                                                    self.ismatchany,
                                                                                    self.doublecolon)

class PatternRule(object):
    """
    An implicit rule or static pattern rule containing target patterns, prerequisite patterns,
    and a list of commands.
    """

    def __init__(self, targetpatterns, prerequisites, doublecolon, loc):
        self.targetpatterns = targetpatterns
        self.prerequisites = prerequisites
        self.doublecolon = doublecolon
        self.loc = loc
        self.commands = []

    def addcommand(self, c):
        assert isinstance(c, (Expansion, StringExpansion))
        self.commands.append(c)

    def ismatchany(self):
        return util.any((t.ismatchany() for t in self.targetpatterns))

    def hasspecificmatch(self, file):
        for p in self.targetpatterns:
            if not p.ismatchany() and p.match(file) is not None:
                return True

        return False

    def matchesfor(self, dir, file, skipsinglecolonmatchany):
        """
        Determine all the target patterns of this rule that might match target t.
        @yields a PatternRuleInstance for each.
        """

        for p in self.targetpatterns:
            matchany = p.ismatchany()
            if matchany:
                if skipsinglecolonmatchany and not self.doublecolon:
                    continue

                yield PatternRuleInstance(self, dir, file, True)
            else:
                stem = p.match(dir + file)
                if stem is not None:
                    yield PatternRuleInstance(self, '', stem, False)
                else:
                    stem = p.match(file)
                    if stem is not None:
                        yield PatternRuleInstance(self, dir, stem, False)

    def prerequisitesforstem(self, dir, stem):
        return [p.resolve(dir, stem) for p in self.prerequisites]

class _RemakeContext(object):
    def __init__(self, makefile, cb):
        self.makefile = makefile
        self.included = [(makefile.gettarget(f), required)
                         for f, required in makefile.included]
        self.toremake = list(self.included)
        self.cb = cb

        self.remakecb(error=False, didanything=False)

    def remakecb(self, error, didanything):
        assert error in (True, False)

        if error:
            if self.required:
                self.cb(remade=False, error=errors.MakeError(
                    'Error remaking required makefiles'))
                return
            else:
                print('Error remaking makefiles (ignored)')

        if len(self.toremake):
            target, self.required = self.toremake.pop(0)
            target.make(self.makefile, [], avoidremakeloop=True, cb=self.remakecb, printerror=False)
        else:
            for t, required in self.included:
                if t.wasremade:
                    _data_log.info("Included file %s was remade, restarting make", t.target)
                    self.cb(remade=True)
                    return
                elif required and t.mtime is None:
                    self.cb(remade=False, error=errors.DataError("No rule to remake missing include file %s" % t.target))
                    return

            self.cb(remade=False)

class Makefile(object):
    """
    The top-level data structure for makefile execution. It holds Targets, implicit rules, and other
    state data.
    """

    def __init__(self, workdir=None, env=None, restarts=0, make=None,
                 makeflags='', makeoverrides='',
                 makelevel=0, context=None, targets=(), keepgoing=False,
                 silent=False, justprint=False):
        self.defaulttarget = None

        if env is None:
            env = os.environ
        self.env = env

        self.variables = Variables()
        self.variables.readfromenvironment(env)

        self.context = context
        self.exportedvars = {}
        self._targets = {}
        self.keepgoing = keepgoing
        self.silent = silent
        self.justprint = justprint
        self._patternvariables = [] # of (pattern, variables)
        self.implicitrules = []
        self.parsingfinished = False

        self._patternvpaths = [] # of (pattern, [dir, ...])

        if workdir is None:
            workdir = os.getcwd()
        workdir = os.path.realpath(workdir)
        self.workdir = workdir
        self.variables.set('CURDIR', Variables.FLAVOR_SIMPLE,
                           Variables.SOURCE_AUTOMATIC, workdir.replace('\\','/'))

        # the list of included makefiles, whether or not they existed
        self.included = []

        self.variables.set('MAKE_RESTARTS', Variables.FLAVOR_SIMPLE,
                           Variables.SOURCE_AUTOMATIC, restarts > 0 and str(restarts) or '')

        self.variables.set('.PYMAKE', Variables.FLAVOR_SIMPLE,
                           Variables.SOURCE_MAKEFILE, "1")
        if make is not None:
            self.variables.set('MAKE', Variables.FLAVOR_SIMPLE,
                               Variables.SOURCE_MAKEFILE, make)

        if makeoverrides != '':
            self.variables.set('-*-command-variables-*-', Variables.FLAVOR_SIMPLE,
                               Variables.SOURCE_AUTOMATIC, makeoverrides)
            makeflags += ' -- $(MAKEOVERRIDES)'

        self.variables.set('MAKEOVERRIDES', Variables.FLAVOR_RECURSIVE,
                           Variables.SOURCE_ENVIRONMENT,
                           '${-*-command-variables-*-}')

        self.variables.set('MAKEFLAGS', Variables.FLAVOR_RECURSIVE,
                           Variables.SOURCE_MAKEFILE, makeflags)
        self.exportedvars['MAKEFLAGS'] = True

        self.makelevel = makelevel
        self.variables.set('MAKELEVEL', Variables.FLAVOR_SIMPLE,
                           Variables.SOURCE_MAKEFILE, str(makelevel))

        self.variables.set('MAKECMDGOALS', Variables.FLAVOR_SIMPLE,
                           Variables.SOURCE_AUTOMATIC, ' '.join(targets))

        for vname, val in implicit.variables.items():
            self.variables.set(vname,
                               Variables.FLAVOR_SIMPLE,
                               Variables.SOURCE_IMPLICIT, val)

    def foundtarget(self, t):
        """
        Inform the makefile of a target which is a candidate for being the default target,
        if there isn't already a default target.
        """
        flavor, source, value = self.variables.get('.DEFAULT_GOAL')
        if self.defaulttarget is None and t != '.PHONY' and value is None:
            self.defaulttarget = t
            self.variables.set('.DEFAULT_GOAL', Variables.FLAVOR_SIMPLE,
                               Variables.SOURCE_AUTOMATIC, t)

    def getpatternvariables(self, pattern):
        assert isinstance(pattern, Pattern)

        for p, v in self._patternvariables:
            if p == pattern:
                return v

        v = Variables()
        self._patternvariables.append( (pattern, v) )
        return v

    def getpatternvariablesfor(self, target):
        for p, v in self._patternvariables:
            if p.match(target):
                yield v

    def hastarget(self, target):
        return target in self._targets

    _globcheck = re.compile('[[*?]')
    def gettarget(self, target):
        assert isinstance(target, str_type)

        target = target.rstrip('/')

        assert target != '', "empty target?"

        assert not self._globcheck.match(target)

        t = self._targets.get(target, None)
        if t is None:
            t = Target(target, self)
            self._targets[target] = t
        return t

    def appendimplicitrule(self, rule):
        assert isinstance(rule, PatternRule)
        self.implicitrules.append(rule)

    def finishparsing(self):
        """
        Various activities, such as "eval", are not allowed after parsing is
        finished. In addition, various warnings and errors can only be issued
        after the parsing data model is complete. All dependency resolution
        and rule execution requires that parsing be finished.
        """
        self.parsingfinished = True

        flavor, source, value = self.variables.get('GPATH')
        if value is not None and value.resolvestr(self, self.variables, ['GPATH']).strip() != '':
            raise errors.DataError('GPATH was set: pymake does not support GPATH semantics')

        flavor, source, value = self.variables.get('VPATH')
        if value is None:
            self._vpath = []
        else:
            self._vpath = [e for e in re.split('[%s\s]+' % os.pathsep,
                                          value.resolvestr(self, self.variables, ['VPATH'])) if e != '']

        # Must materialize target values because
        # gettarget() modifies self._targets.
        targets = list(self._targets.values())
        for t in targets:
            t.explicit = True
            for r in t.rules:
                for p in r.prerequisites:
                    self.gettarget(p).explicit = True

        np = self.gettarget('.NOTPARALLEL')
        if len(np.rules):
            self.context = process.getcontext(1)

        flavor, source, value = self.variables.get('.DEFAULT_GOAL')
        if value is not None:
            self.defaulttarget = value.resolvestr(self, self.variables, ['.DEFAULT_GOAL']).strip()

        self.error = False

    def include(self, path, required=True, weak=False, loc=None):
        """
        Include the makefile at `path`.
        """
        if self._globcheck.search(path):
            paths = glob(self.workdir, path)
        else:
            paths = [path]
        for path in paths:
            self.included.append((path, required))
            fspath = util.normaljoin(self.workdir, path)
            if os.path.exists(fspath):
                if weak:
                    stmts = parsedepfile(fspath)
                else:
                    stmts = parsefile(fspath)
                self.variables.append('MAKEFILE_LIST', Variables.SOURCE_AUTOMATIC, path, None, self)
                stmts.execute(self, weak=weak)
                self.gettarget(path).explicit = True

    def addvpath(self, pattern, dirs):
        """
        Add a directory to the vpath search for the given pattern.
        """
        self._patternvpaths.append((pattern, dirs))

    def clearvpath(self, pattern):
        """
        Clear vpaths for the given pattern.
        """
        self._patternvpaths = [(p, dirs)
                               for p, dirs in self._patternvpaths
                               if not p.match(pattern)]

    def clearallvpaths(self):
        self._patternvpaths = []

    def getvpath(self, target):
        vp = list(self._vpath)
        for p, dirs in self._patternvpaths:
            if p.match(target):
                vp.extend(dirs)

        return withoutdups(vp)

    def remakemakefiles(self, cb):
        mlist = []
        for f, required in self.included:
            t = self.gettarget(f)
            t.explicit = True
            t.resolvevpath(self)
            oldmtime = t.mtime

            mlist.append((t, oldmtime))

        _RemakeContext(self, cb)

    def getsubenvironment(self, variables):
        env = dict(self.env)
        for vname, v in self.exportedvars.items():
            if v:
                flavor, source, val = variables.get(vname)
                if val is None:
                    strval = ''
                else:
                    strval = val.resolvestr(self, variables, [vname])
                env[vname] = strval
            else:
                env.pop(vname, None)

        makeflags = ''

        env['MAKELEVEL'] = str(self.makelevel + 1)
        return env


"""
Makefile functions.
"""
def emit_expansions(descend, *expansions):
    """Helper function to emit all expansions within an input set."""
    for expansion in expansions:
        yield expansion

        if not descend or not isinstance(expansion, list):
            continue

        for e, is_func in expansion:
            if is_func:
                for exp in e.expansions(True):
                    yield exp
            else:
                yield e

class Function(object):
    """
    An object that represents a function call. This class is always subclassed
    with the following methods and attributes:

    minargs = minimum # of arguments
    maxargs = maximum # of arguments (0 means unlimited)

    def resolve(self, makefile, variables, fd, setting)
        Calls the function
        calls fd.write() with strings
    """

    __slots__ = ('_arguments', 'loc')

    def __init__(self, loc):
        self._arguments = []
        self.loc = loc
        assert self.minargs > 0

    def __getitem__(self, key):
        return self._arguments[key]

    def setup(self):
        argc = len(self._arguments)

        if argc < self.minargs:
            raise errors.DataError("Not enough arguments to function %s, requires %s" % (self.name, self.minargs), self.loc)

        assert self.maxargs == 0 or argc <= self.maxargs, "Parser screwed up, gave us too many args"

    def append(self, arg):
        assert isinstance(arg, (Expansion, StringExpansion))
        self._arguments.append(arg)

    def to_source(self):
        """Convert the function back to make file "source" code."""
        if not hasattr(self, 'name'):
            raise Exception("%s must implement to_source()." % self.__class__)

        # The default implementation simply prints the function name and all
        # the arguments joined by a comma.
        # According to the GNU make manual Section 8.1, whitespace around
        # arguments is *not* part of the argument's value. So, we trim excess
        # white space so we have consistent behavior.
        args = []
        curly = False
        for i, arg in enumerate(self._arguments):
            arg = arg.to_source()

            if i == 0:
                arg = arg.lstrip()

            # Are balanced parens even OK?
            if arg.count('(') != arg.count(')'):
                curly = True

            args.append(arg)

        if curly:
            return '${%s %s}' % (self.name, ','.join(args))

        return '$(%s %s)' % (self.name, ','.join(args))

    def expansions(self, descend=False):
        """Obtain all expansions contained within this function.

        By default, only expansions directly part of this function are
        returned. If descend is True, we will descend into child expansions and
        return all of the composite parts.

        This is a generator for pymake.engine.BaseExpansion instances.
        """
        # Our default implementation simply returns arguments. More advanced
        # functions like variable references may need their own implementation.
        return emit_expansions(descend, *self._arguments)

    @property
    def is_filesystem_dependent(self):
        """Exposes whether this function depends on the filesystem for results.

        If True, the function touches the filesystem as part of evaluation.

        This only tests whether the function itself uses the filesystem. If
        this function has arguments that are functions that touch the
        filesystem, this will return False.
        """
        return False

    def __len__(self):
        return len(self._arguments)

    def __repr__(self):
        return "%s<%s>(%r)" % (
            self.__class__.__name__, self.loc,
            ','.join([repr(a) for a in self._arguments]),
            )

    def __eq__(self, other):
        if not hasattr(self, 'name'):
            raise Exception("%s must implement __eq__." % self.__class__)

        if type(self) != type(other):
            return False

        if self.name != other.name:
            return False

        if len(self._arguments) != len(other._arguments):
            return False

        for i in range(len(self._arguments)):
            # According to the GNU make manual Section 8.1, whitespace around
            # arguments is *not* part of the argument's value. So, we do a
            # whitespace-agnostic comparison.
            if i == 0:
                a = self._arguments[i]
                a.lstrip()

                b = other._arguments[i]
                b.lstrip()

                if a != b:
                    return False

                continue

            if self._arguments[i] != other._arguments[i]:
                return False

        return True

    def __ne__(self, other):
        return not self.__eq__(other)

class VariableRef(Function):
    AUTOMATIC_VARIABLES = set(['@', '%', '<', '?', '^', '+', '|', '*'])

    __slots__ = ('vname', 'loc')

    def __init__(self, loc, vname):
        self.loc = loc
        assert isinstance(vname, (Expansion, StringExpansion))
        self.vname = vname

    def setup(self):
        assert False, "Shouldn't get here"

    def resolve(self, makefile, variables, fd, setting):
        vname = self.vname.resolvestr(makefile, variables, setting)
        if vname in setting:
            raise errors.DataError("Setting variable '%s' recursively references itself." % (vname,), self.loc)

        flavor, source, value = variables.get(vname)
        if value is None:
            _data_log.debug("%s: variable '%s' was not set" % (self.loc, vname))
            return

        value.resolve(makefile, variables, fd, setting + [vname])

    def to_source(self):
        if isinstance(self.vname, StringExpansion):
            if self.vname.s in self.AUTOMATIC_VARIABLES:
                return '$%s' % self.vname.s

            return '$(%s)' % self.vname.s

        return '$(%s)' % self.vname.to_source()

    def expansions(self, descend=False):
        return emit_expansions(descend, self.vname)

    def __repr__(self):
        return "VariableRef<%s>(%r)" % (self.loc, self.vname)

    def __eq__(self, other):
        if not isinstance(other, VariableRef):
            return False

        return self.vname == other.vname

class SubstitutionRef(Function):
    """$(VARNAME:.c=.o) and $(VARNAME:%.c=%.o)"""

    __slots__ = ('loc', 'vname', 'substfrom', 'substto')

    def __init__(self, loc, varname, substfrom, substto):
        self.loc = loc
        self.vname = varname
        self.substfrom = substfrom
        self.substto = substto

    def setup(self):
        assert False, "Shouldn't get here"

    def resolve(self, makefile, variables, fd, setting):
        vname = self.vname.resolvestr(makefile, variables, setting)
        if vname in setting:
            raise errors.DataError("Setting variable '%s' recursively references itself." % (vname,), self.loc)

        substfrom = self.substfrom.resolvestr(makefile, variables, setting)
        substto = self.substto.resolvestr(makefile, variables, setting)

        flavor, source, value = variables.get(vname)
        if value is None:
            _data_log.debug("%s: variable '%s' was not set" % (self.loc, vname))
            return

        f = Pattern(substfrom)
        if not f.ispattern():
            f = Pattern('%' + substfrom)
            substto = '%' + substto

        fd.write(' '.join([f.subst(substto, word, False)
                           for word in value.resolvesplit(makefile, variables, setting + [vname])]))

    def to_source(self):
        return '$(%s:%s=%s)' % (
            self.vname.to_source(),
            self.substfrom.to_source(),
            self.substto.to_source())

    def expansions(self, descend=False):
        return emit_expansions(descend, self.vname, self.substfrom,
                self.substto)

    def __repr__(self):
        return "SubstitutionRef<%s>(%r:%r=%r)" % (
            self.loc, self.vname, self.substfrom, self.substto,)

    def __eq__(self, other):
        if not isinstance(other, SubstitutionRef):
            return False

        return self.vname == other.vname and self.substfrom == other.substfrom \
                and self.substto == other.substto

class SubstFunction(Function):
    name = 'subst'
    minargs = 3
    maxargs = 3

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        s = self._arguments[0].resolvestr(makefile, variables, setting)
        r = self._arguments[1].resolvestr(makefile, variables, setting)
        d = self._arguments[2].resolvestr(makefile, variables, setting)
        fd.write(d.replace(s, r))

class PatSubstFunction(Function):
    name = 'patsubst'
    minargs = 3
    maxargs = 3

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        s = self._arguments[0].resolvestr(makefile, variables, setting)
        r = self._arguments[1].resolvestr(makefile, variables, setting)

        p = Pattern(s)
        fd.write(' '.join([p.subst(r, word, False)
                           for word in self._arguments[2].resolvesplit(makefile, variables, setting)]))

class StripFunction(Function):
    name = 'strip'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        util.joiniter(fd, self._arguments[0].resolvesplit(makefile, variables, setting))

class FindstringFunction(Function):
    name = 'findstring'
    minargs = 2
    maxargs = 2

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        s = self._arguments[0].resolvestr(makefile, variables, setting)
        r = self._arguments[1].resolvestr(makefile, variables, setting)
        if r.find(s) == -1:
            return
        fd.write(s)

class FilterFunction(Function):
    name = 'filter'
    minargs = 2
    maxargs = 2

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        plist = [Pattern(p)
                 for p in self._arguments[0].resolvesplit(makefile, variables, setting)]

        fd.write(' '.join([w for w in self._arguments[1].resolvesplit(makefile, variables, setting)
                           if util.any((p.match(w) for p in plist))]))

class FilteroutFunction(Function):
    name = 'filter-out'
    minargs = 2
    maxargs = 2

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        plist = [Pattern(p)
                 for p in self._arguments[0].resolvesplit(makefile, variables, setting)]

        fd.write(' '.join([w for w in self._arguments[1].resolvesplit(makefile, variables, setting)
                           if not util.any((p.match(w) for p in plist))]))

class SortFunction(Function):
    name = 'sort'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        d = set(self._arguments[0].resolvesplit(makefile, variables, setting))
        util.joiniter(fd, sorted(d))

class WordFunction(Function):
    name = 'word'
    minargs = 2
    maxargs = 2

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        n = self._arguments[0].resolvestr(makefile, variables, setting)
        # TODO: provide better error if this doesn't convert
        n = int(n)
        words = list(self._arguments[1].resolvesplit(makefile, variables, setting))
        if n < 1 or n > len(words):
            return
        fd.write(words[n - 1])

class WordlistFunction(Function):
    name = 'wordlist'
    minargs = 3
    maxargs = 3

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        nfrom = self._arguments[0].resolvestr(makefile, variables, setting)
        nto = self._arguments[1].resolvestr(makefile, variables, setting)
        # TODO: provide better errors if this doesn't convert
        nfrom = int(nfrom)
        nto = int(nto)

        words = list(self._arguments[2].resolvesplit(makefile, variables, setting))

        if nfrom < 1:
            nfrom = 1
        if nto < 1:
            nto = 1

        util.joiniter(fd, words[nfrom - 1:nto])

class WordsFunction(Function):
    name = 'words'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        fd.write(str(len(self._arguments[0].resolvesplit(makefile, variables, setting))))

class FirstWordFunction(Function):
    name = 'firstword'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        l = self._arguments[0].resolvesplit(makefile, variables, setting)
        if len(l):
            fd.write(l[0])

class LastWordFunction(Function):
    name = 'lastword'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        l = self._arguments[0].resolvesplit(makefile, variables, setting)
        if len(l):
            fd.write(l[-1])

def pathsplit(path, default='./'):
    """
    Splits a path into dirpart, filepart on the last slash. If there is no slash, dirpart
    is ./
    """
    dir, slash, file = util.strrpartition(path, '/')
    if dir == '':
        return default, file

    return dir + slash, file

class DirFunction(Function):
    name = 'dir'
    minargs = 1
    maxargs = 1

    def resolve(self, makefile, variables, fd, setting):
        fd.write(' '.join([pathsplit(path)[0]
                           for path in self._arguments[0].resolvesplit(makefile, variables, setting)]))

class NotDirFunction(Function):
    name = 'notdir'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        fd.write(' '.join([pathsplit(path)[1]
                           for path in self._arguments[0].resolvesplit(makefile, variables, setting)]))

class SuffixFunction(Function):
    name = 'suffix'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    @staticmethod
    def suffixes(words):
        for w in words:
            dir, file = pathsplit(w)
            base, dot, suffix = util.strrpartition(file, '.')
            if base != '':
                yield dot + suffix

    def resolve(self, makefile, variables, fd, setting):
        util.joiniter(fd, self.suffixes(self._arguments[0].resolvesplit(makefile, variables, setting)))

class BasenameFunction(Function):
    name = 'basename'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    @staticmethod
    def basenames(words):
        for w in words:
            dir, file = pathsplit(w, '')
            base, dot, suffix = util.strrpartition(file, '.')
            if dot == '':
                base = suffix

            yield dir + base

    def resolve(self, makefile, variables, fd, setting):
        util.joiniter(fd, self.basenames(self._arguments[0].resolvesplit(makefile, variables, setting)))

class AddSuffixFunction(Function):
    name = 'addsuffix'
    minargs = 2
    maxargs = 2

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        suffix = self._arguments[0].resolvestr(makefile, variables, setting)

        fd.write(' '.join([w + suffix for w in self._arguments[1].resolvesplit(makefile, variables, setting)]))

class AddPrefixFunction(Function):
    name = 'addprefix'
    minargs = 2
    maxargs = 2

    def resolve(self, makefile, variables, fd, setting):
        prefix = self._arguments[0].resolvestr(makefile, variables, setting)

        fd.write(' '.join([prefix + w for w in self._arguments[1].resolvesplit(makefile, variables, setting)]))

class JoinFunction(Function):
    name = 'join'
    minargs = 2
    maxargs = 2

    __slots__ = Function.__slots__

    @staticmethod
    def iterjoin(l1, l2):
        for i in range(0, max(len(l1), len(l2))):
            i1 = i < len(l1) and l1[i] or ''
            i2 = i < len(l2) and l2[i] or ''
            yield i1 + i2

    def resolve(self, makefile, variables, fd, setting):
        list1 = list(self._arguments[0].resolvesplit(makefile, variables, setting))
        list2 = list(self._arguments[1].resolvesplit(makefile, variables, setting))

        util.joiniter(fd, self.iterjoin(list1, list2))

class WildcardFunction(Function):
    name = 'wildcard'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        patterns = self._arguments[0].resolvesplit(makefile, variables, setting)

        fd.write(' '.join([x.replace('\\','/')
                           for p in patterns
                           for x in glob(makefile.workdir, p)]))

    @property
    def is_filesystem_dependent(self):
        return True

class RealpathFunction(Function):
    name = 'realpath'
    minargs = 1
    maxargs = 1

    def resolve(self, makefile, variables, fd, setting):
        fd.write(' '.join([os.path.realpath(os.path.join(makefile.workdir, path)).replace('\\', '/')
                           for path in self._arguments[0].resolvesplit(makefile, variables, setting)]))

    def is_filesystem_dependent(self):
        return True

class AbspathFunction(Function):
    name = 'abspath'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        assert os.path.isabs(makefile.workdir)
        fd.write(' '.join([util.normaljoin(makefile.workdir, path).replace('\\', '/')
                           for path in self._arguments[0].resolvesplit(makefile, variables, setting)]))

class IfFunction(Function):
    name = 'if'
    minargs = 1
    maxargs = 3

    __slots__ = Function.__slots__

    def setup(self):
        Function.setup(self)
        self._arguments[0].lstrip()
        self._arguments[0].rstrip()

    def resolve(self, makefile, variables, fd, setting):
        condition = self._arguments[0].resolvestr(makefile, variables, setting)

        if len(condition):
            self._arguments[1].resolve(makefile, variables, fd, setting)
        elif len(self._arguments) > 2:
            return self._arguments[2].resolve(makefile, variables, fd, setting)

class OrFunction(Function):
    name = 'or'
    minargs = 1
    maxargs = 0

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        for arg in self._arguments:
            r = arg.resolvestr(makefile, variables, setting)
            if r != '':
                fd.write(r)
                return

class AndFunction(Function):
    name = 'and'
    minargs = 1
    maxargs = 0

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        r = ''

        for arg in self._arguments:
            r = arg.resolvestr(makefile, variables, setting)
            if r == '':
                return

        fd.write(r)

class ForEachFunction(Function):
    name = 'foreach'
    minargs = 3
    maxargs = 3

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        vname = self._arguments[0].resolvestr(makefile, variables, setting)
        e = self._arguments[2]

        v = Variables(parent=variables)
        firstword = True

        for w in self._arguments[1].resolvesplit(makefile, variables, setting):
            if firstword:
                firstword = False
            else:
                fd.write(' ')

            # The $(origin) of the local variable must be "automatic" to
            # conform with GNU make. However, automatic variables have low
            # priority. So, we must force its assignment to occur.
            v.set(vname, Variables.FLAVOR_SIMPLE,
                    Variables.SOURCE_AUTOMATIC, w, force=True)
            e.resolve(makefile, v, fd, setting)

class CallFunction(Function):
    name = 'call'
    minargs = 1
    maxargs = 0

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        vname = self._arguments[0].resolvestr(makefile, variables, setting)
        if vname in setting:
            raise errors.DataError("Recursively setting variable '%s'" % (vname,))

        v = Variables(parent=variables)
        v.set('0', Variables.FLAVOR_SIMPLE, Variables.SOURCE_AUTOMATIC, vname)
        for i in range(1, len(self._arguments)):
            param = self._arguments[i].resolvestr(makefile, variables, setting)
            v.set(str(i), Variables.FLAVOR_SIMPLE, Variables.SOURCE_AUTOMATIC, param)

        flavor, source, e = variables.get(vname)

        if e is None:
            return

        if flavor == Variables.FLAVOR_SIMPLE:
            _data_log.warning("%s: calling variable '%s' which is simply-expanded" % (self.loc, vname))

        # but we'll do it anyway
        e.resolve(makefile, v, fd, setting + [vname])

class ValueFunction(Function):
    name = 'value'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        varname = self._arguments[0].resolvestr(makefile, variables, setting)

        flavor, source, value = variables.get(varname, expand=False)
        if value is not None:
            fd.write(value)

class EvalFunction(Function):
    name = 'eval'
    minargs = 1
    maxargs = 1

    def resolve(self, makefile, variables, fd, setting):
        if makefile.parsingfinished:
            # GNU make allows variables to be set by recursive expansion during
            # command execution. This seems really dumb to me, so I don't!
            raise errors.DataError("$(eval) not allowed via recursive expansion after parsing is finished", self.loc)

        stmts = parsestring(self._arguments[0].resolvestr(makefile, variables, setting),
                                   'evaluation from %s' % self.loc)
        stmts.execute(makefile)

class OriginFunction(Function):
    name = 'origin'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        vname = self._arguments[0].resolvestr(makefile, variables, setting)

        flavor, source, value = variables.get(vname)
        if source is None:
            r = 'undefined'
        elif source == Variables.SOURCE_OVERRIDE:
            r = 'override'

        elif source == Variables.SOURCE_MAKEFILE:
            r = 'file'
        elif source == Variables.SOURCE_ENVIRONMENT:
            r = 'environment'
        elif source == Variables.SOURCE_COMMANDLINE:
            r = 'command line'
        elif source == Variables.SOURCE_AUTOMATIC:
            r = 'automatic'
        elif source == Variables.SOURCE_IMPLICIT:
            r = 'default'

        fd.write(r)

class FlavorFunction(Function):
    name = 'flavor'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        varname = self._arguments[0].resolvestr(makefile, variables, setting)
        
        flavor, source, value = variables.get(varname)
        if flavor is None:
            r = 'undefined'
        elif flavor == Variables.FLAVOR_RECURSIVE:
            r = 'recursive'
        elif flavor == Variables.FLAVOR_SIMPLE:
            r = 'simple'
        fd.write(r)

class ShellFunction(Function):
    name = 'shell'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        cline = self._arguments[0].resolvestr(makefile, variables, setting)
        executable, cline = process.prepare_command(cline, makefile.workdir, self.loc)

        # subprocess.Popen doesn't use the PATH set in the env argument for
        # finding the executable on some platforms (but strangely it does on
        # others!), so set os.environ['PATH'] explicitly.
        oldpath = os.environ['PATH']
        if makefile.env is not None and 'PATH' in makefile.env:
            os.environ['PATH'] = makefile.env['PATH']

        _data_log.debug("%s: running command '%s'" % (self.loc, ' '.join(cline)))
        try:
            p = subprocess.Popen(cline, executable=executable, env=makefile.env, shell=False,
                                 stdout=subprocess.PIPE, cwd=makefile.workdir)
        except OSError as e:
            print("Error executing command %s" % cline[0], e, file=sys.stderr)
            return
        finally:
            os.environ['PATH'] = oldpath

        stdout, stderr = p.communicate()
        stdout = stdout.replace('\r\n', '\n')
        if stdout.endswith('\n'):
            stdout = stdout[:-1]
        stdout = stdout.replace('\n', ' ')

        fd.write(stdout)

class ErrorFunction(Function):
    name = 'error'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        v = self._arguments[0].resolvestr(makefile, variables, setting)
        raise errors.DataError(v, self.loc)

class WarningFunction(Function):
    name = 'warning'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        v = self._arguments[0].resolvestr(makefile, variables, setting)
        _data_log.warning(v)

class InfoFunction(Function):
    name = 'info'
    minargs = 1
    maxargs = 1

    __slots__ = Function.__slots__

    def resolve(self, makefile, variables, fd, setting):
        v = self._arguments[0].resolvestr(makefile, variables, setting)
        print(v)

functionmap = {
    'subst': SubstFunction,
    'patsubst': PatSubstFunction,
    'strip': StripFunction,
    'findstring': FindstringFunction,
    'filter': FilterFunction,
    'filter-out': FilteroutFunction,
    'sort': SortFunction,
    'word': WordFunction,
    'wordlist': WordlistFunction,
    'words': WordsFunction,
    'firstword': FirstWordFunction,
    'lastword': LastWordFunction,
    'dir': DirFunction,
    'notdir': NotDirFunction,
    'suffix': SuffixFunction,
    'basename': BasenameFunction,
    'addsuffix': AddSuffixFunction,
    'addprefix': AddPrefixFunction,
    'join': JoinFunction,
    'wildcard': WildcardFunction,
    'realpath': RealpathFunction,
    'abspath': AbspathFunction,
    'if': IfFunction,
    'or': OrFunction,
    'and': AndFunction,
    'foreach': ForEachFunction,
    'call': CallFunction,
    'value': ValueFunction,
    'eval': EvalFunction,
    'origin': OriginFunction,
    'flavor': FlavorFunction,
    'shell': ShellFunction,
    'error': ErrorFunction,
    'warning': WarningFunction,
    'info': InfoFunction,
}


"""
Parser data structures.
"""
_tabwidth = 4

class Location(object):
    """
    A location within a makefile.

    For the moment, locations are just path/line/column, but in the future
    they may reference parent locations for more accurate "included from"
    or "evaled at" error reporting.
    """
    __slots__ = ('path', 'line', 'column')

    def __init__(self, path, line, column):
        self.path = path
        self.line = line
        self.column = column

    def offset(self, s, start, end):
        """
        Returns a new location offset by
        the specified string.
        """

        if start == end:
            return self

        skiplines = s.count('\n', start, end)
        line = self.line + skiplines
        if skiplines:
            lastnl = s.rfind('\n', start, end)
            assert lastnl != -1
            start = lastnl + 1
            column = 0
        else:
            column = self.column

        while True:
            j = s.find('\t', start, end)
            if j == -1:
                column += end - start
                break

            column += j - start
            column += _tabwidth
            column -= column % _tabwidth
            start = j + 1

        return Location(self.path, line, column)

    def __str__(self):
        return "%s:%s:%s" % (self.path, self.line, self.column)

def _expandwildcards(makefile, tlist):
    for t in tlist:
        if not hasglob(t):
            yield t
        else:
            l = glob(makefile.workdir, t)
            for r in l:
                yield r

_flagescape = re.compile(r'([\s\\])')

def parsecommandlineargs(args):
    """
    Given a set of arguments from a command-line invocation of make,
    parse out the variable definitions and return (stmts, arglist, overridestr)
    """

    overrides = []
    stmts = StatementList()
    r = []
    for i in range(0, len(args)):
        a = args[i]

        vname, t, val = util.strpartition(a, ':=')
        if t == '':
            vname, t, val = util.strpartition(a, '=')
        if t != '':
            overrides.append(_flagescape.sub(r'\\\1', a))

            vname = vname.strip()
            vnameexp = Expansion.fromstring(vname, "Command-line argument")

            stmts.append(ExportDirective(vnameexp, concurrent_set=True))
            stmts.append(SetVariable(vnameexp, token=t,
                                     value=val, valueloc=Location('<command-line>', i, len(vname) + len(t)),
                                     targetexp=None, source=Variables.SOURCE_COMMANDLINE))
        else:
            r.append(stripdotslash(a))

    return stmts, r, ' '.join(overrides)

class Statement(object):
    """
    Represents parsed make file syntax.

    This is an abstract base class. Child classes are expected to implement
    basic methods defined below.
    """

    def execute(self, makefile, context):
        """Executes this Statement within a make file execution context."""
        raise Exception("%s must implement execute()." % self.__class__)

    def to_source(self):
        """Obtain the make file "source" representation of the Statement.

        This converts an individual Statement back to a string that can again
        be parsed into this Statement.
        """
        raise Exception("%s must implement to_source()." % self.__class__)

    def __eq__(self, other):
        raise Exception("%s must implement __eq__." % self.__class__)

    def __ne__(self, other):
        return self.__eq__(other)

class DummyRule(object):
    __slots__ = ()

    def addcommand(self, r):
        pass

class RuleStatement(Statement):
    """
    Rules represent how to make specific targets.

    See https://www.gnu.org/software/make/manual/make.html#Rules.

    An individual rule is composed of a target, dependencies, and a recipe.
    This class only contains references to the first 2. The recipe will be
    contained in Command classes which follow this one in a stream of Statement
    instances.

    Instances also contain a boolean property `doublecolon` which says whether
    this is a doublecolon rule. Doublecolon rules are rules that are always
    executed, if they are evaluated. Normally, rules are only executed if their
    target is out of date.
    """
    __slots__ = ('targetexp', 'depexp', 'doublecolon')

    def __init__(self, targetexp, depexp, doublecolon):
        assert isinstance(targetexp, (Expansion, StringExpansion))
        assert isinstance(depexp, (Expansion, StringExpansion))

        self.targetexp = targetexp
        self.depexp = depexp
        self.doublecolon = doublecolon

    def execute(self, makefile, context):
        if context.weak:
            self._executeweak(makefile, context)
        else:
            self._execute(makefile, context)

    def _executeweak(self, makefile, context):
        """
        If the context is weak (we're just handling dependencies) we can make a number of assumptions here.
        This lets us go really fast and is generally good.
        """
        assert context.weak
        deps = self.depexp.resolvesplit(makefile, makefile.variables)
        # Skip targets with no rules and no dependencies
        if not deps:
            return
        targets = stripdotslashes(self.targetexp.resolvesplit(makefile, makefile.variables))
        rule = Rule(list(stripdotslashes(deps)), self.doublecolon, loc=self.targetexp.loc, weakdeps=True)
        for target in targets:
            makefile.gettarget(target).addrule(rule)
            makefile.foundtarget(target)
        context.currule = rule

    def _execute(self, makefile, context):
        assert not context.weak

        atargets = stripdotslashes(self.targetexp.resolvesplit(makefile, makefile.variables))
        targets = [Pattern(p) for p in _expandwildcards(makefile, atargets)]

        if not len(targets):
            context.currule = DummyRule()
            return

        ispatterns = set((t.ispattern() for t in targets))
        if len(ispatterns) == 2:
            raise errors.DataError("Mixed implicit and normal rule", self.targetexp.loc)
        ispattern, = ispatterns

        deps = list(_expandwildcards(makefile, stripdotslashes(self.depexp.resolvesplit(makefile, makefile.variables))))
        if ispattern:
            prerequisites = [Pattern(d) for d in deps]
            rule = PatternRule(targets, prerequisites, self.doublecolon, loc=self.targetexp.loc)
            makefile.appendimplicitrule(rule)
        else:
            rule = Rule(deps, self.doublecolon, loc=self.targetexp.loc, weakdeps=False)
            for t in targets:
                makefile.gettarget(t.gettarget()).addrule(rule)

            makefile.foundtarget(targets[0].gettarget())

        context.currule = rule

    def dump(self, fd, indent):
        print("%sRule %s: %s" % (indent, self.targetexp, self.depexp), file=fd)

    def to_source(self):
        sep = ':'

        if self.doublecolon:
            sep = '::'

        deps = self.depexp.to_source()
        if len(deps) > 0 and not deps[0].isspace():
            sep += ' '

        return '\n%s%s%s' % (
            self.targetexp.to_source(escape_variables=True),
            sep,
            deps)

    def __eq__(self, other):
        if not isinstance(other, RuleStatement):
            return False

        return self.targetexp == other.targetexp \
                and self.depexp == other.depexp \
                and self.doublecolon == other.doublecolon

class StaticPatternRule(Statement):
    """
    Static pattern rules are rules which specify multiple targets based on a
    string pattern.

    See https://www.gnu.org/software/make/manual/make.html#Static-Pattern

    They are like `RuleStatement` instances except an added property, `patternexp` is
    present. It contains the Expansion which represents the rule pattern.
    """
    __slots__ = ('targetexp', 'patternexp', 'depexp', 'doublecolon')

    def __init__(self, targetexp, patternexp, depexp, doublecolon):
        assert isinstance(targetexp, (Expansion, StringExpansion))
        assert isinstance(patternexp, (Expansion, StringExpansion))
        assert isinstance(depexp, (Expansion, StringExpansion))

        self.targetexp = targetexp
        self.patternexp = patternexp
        self.depexp = depexp
        self.doublecolon = doublecolon

    def execute(self, makefile, context):
        if context.weak:
            raise errors.DataError("Static pattern rules not allowed in includedeps", self.targetexp.loc)

        targets = list(_expandwildcards(makefile, stripdotslashes(self.targetexp.resolvesplit(makefile, makefile.variables))))

        if not len(targets):
            context.currule = DummyRule()
            return

        patterns = list(stripdotslashes(self.patternexp.resolvesplit(makefile, makefile.variables)))
        if len(patterns) != 1:
            raise errors.DataError("Static pattern rules must have a single pattern", self.patternexp.loc)
        pattern = Pattern(patterns[0])

        deps = [Pattern(p) for p in _expandwildcards(makefile, stripdotslashes(self.depexp.resolvesplit(makefile, makefile.variables)))]

        rule = PatternRule([pattern], deps, self.doublecolon, loc=self.targetexp.loc)

        for t in targets:
            if Pattern(t).ispattern():
                raise errors.DataError("Target '%s' of a static pattern rule must not be a pattern" % (t,), self.targetexp.loc)
            stem = pattern.match(t)
            if stem is None:
                raise errors.DataError("Target '%s' does not match the static pattern '%s'" % (t, pattern), self.targetexp.loc)
            makefile.gettarget(t).addrule(PatternRuleInstance(rule, '', stem, pattern.ismatchany()))

        makefile.foundtarget(targets[0])
        context.currule = rule

    def dump(self, fd, indent):
        print("%sStaticPatternRule %s: %s: %s" % (indent, self.targetexp, self.patternexp, self.depexp), file=fd)

    def to_source(self):
        sep = ':'

        if self.doublecolon:
            sep = '::'

        pattern = self.patternexp.to_source()
        deps = self.depexp.to_source()

        if len(pattern) > 0 and pattern[0] not in (' ', '\t'):
            sep += ' '

        return '\n%s%s%s:%s' % (
            self.targetexp.to_source(escape_variables=True),
            sep,
            pattern,
            deps)

    def __eq__(self, other):
        if not isinstance(other, StaticPatternRule):
            return False

        return self.targetexp == other.targetexp \
                and self.patternexp == other.patternexp \
                and self.depexp == other.depexp \
                and self.doublecolon == other.doublecolon

class Command(Statement):
    """
    Commands are things that get executed by a rule.

    A rule's recipe is composed of 0 or more Commands.

    A command is simply an expansion. Commands typically represent strings to
    be executed in a shell (e.g. via system()). Although, since make files
    allow arbitrary shells to be used for command execution, this isn't a
    guarantee.
    """
    __slots__ = ('exp',)

    def __init__(self, exp):
        assert isinstance(exp, (Expansion, StringExpansion))
        self.exp = exp

    def execute(self, makefile, context):
        assert context.currule is not None
        if context.weak:
            raise errors.DataError("rules not allowed in includedeps", self.exp.loc)

        context.currule.addcommand(self.exp)

    def dump(self, fd, indent):
        print("%sCommand %s" % (indent, self.exp,), file=fd)

    def to_source(self):
        # Commands have some interesting quirks when it comes to source
        # formatting. First, they can be multi-line. Second, a tab needs to be
        # inserted at the beginning of every line. Finally, there might be
        # variable references inside the command. This means we need to escape
        # variable references inside command strings. Luckily, this is handled
        # by the Expansion.
        s = self.exp.to_source(escape_variables=True)

        return '\n'.join(['\t%s' % line for line in s.split('\n')])

    def __eq__(self, other):
        if not isinstance(other, Command):
            return False

        return self.exp == other.exp

class SetVariable(Statement):
    """
    Represents a variable assignment.

    Variable assignment comes in two different flavors.

    Simple assignment has the form:

      <Expansion> <Assignment Token> <string>

    e.g. FOO := bar

    These correspond to the fields `vnameexp`, `token`, and `value`. In
    addition, `valueloc` will be a Location and `source` will be a
    pymake.engine.Variables.SOURCE_* constant.

    There are also target-specific variables. These are variables that only
    apply in the context of a specific target. They are like the aforementioned
    assignment except the `targetexp` field is set to an Expansion representing
    the target they apply to.
    """
    __slots__ = ('vnameexp', 'token', 'value', 'valueloc', 'targetexp', 'source')

    def __init__(self, vnameexp, token, value, valueloc, targetexp, source=None):
        assert isinstance(vnameexp, (Expansion, StringExpansion))
        assert isinstance(value, str)
        assert targetexp is None or isinstance(targetexp, (Expansion, StringExpansion))

        if source is None:
            source = Variables.SOURCE_MAKEFILE

        self.vnameexp = vnameexp
        self.token = token
        self.value = value
        self.valueloc = valueloc
        self.targetexp = targetexp
        self.source = source

    def execute(self, makefile, context):
        vname = self.vnameexp.resolvestr(makefile, makefile.variables)
        if len(vname) == 0:
            raise errors.DataError("Empty variable name", self.vnameexp.loc)

        if self.targetexp is None:
            setvariables = [makefile.variables]
        else:
            setvariables = []

            targets = [Pattern(t) for t in stripdotslashes(self.targetexp.resolvesplit(makefile, makefile.variables))]
            for t in targets:
                if t.ispattern():
                    setvariables.append(makefile.getpatternvariables(t))
                else:
                    setvariables.append(makefile.gettarget(t.gettarget()).variables)

        for v in setvariables:
            if self.token == '+=':
                v.append(vname, self.source, self.value, makefile.variables, makefile)
                continue

            if self.token == '?=':
                flavor = Variables.FLAVOR_RECURSIVE
                oldflavor, oldsource, oldval = v.get(vname, expand=False)
                if oldval is not None:
                    continue
                value = self.value
            elif self.token == '=':
                flavor = Variables.FLAVOR_RECURSIVE
                value = self.value
            else:
                assert self.token == ':='

                flavor = Variables.FLAVOR_SIMPLE
                d = Data.fromstring(self.value, self.valueloc)
                e, t, o = parsemakesyntax(d, 0, (), iterdata)
                value = e.resolvestr(makefile, makefile.variables)

            v.set(vname, flavor, self.source, value)

    def dump(self, fd, indent):
        print("%sSetVariable<%s> %s %s\n%s %r" % (indent, self.valueloc, self.vnameexp, self.token, indent, self.value), file=fd)

    def __eq__(self, other):
        if not isinstance(other, SetVariable):
            return False

        return self.vnameexp == other.vnameexp \
                and self.token == other.token \
                and self.value == other.value \
                and self.targetexp == other.targetexp \
                and self.source == other.source

    def to_source(self):
        chars = []
        for i in range(0, len(self.value)):
            c = self.value[i]

            # Literal # is escaped in variable assignment otherwise it would be
            # a comment.
            if c == '#':
                # If a backslash precedes this, we need to escape it as well.
                if i > 0 and self.value[i-1] == '\\':
                    chars.append('\\')

                chars.append('\\#')
                continue

            chars.append(c)

        value = ''.join(chars)

        prefix = ''
        if self.source == Variables.SOURCE_OVERRIDE:
            prefix = 'override '

        # SetVariable come in two flavors: simple and target-specific.

        # We handle the target-specific syntax first.
        if self.targetexp is not None:
            return '%s: %s %s %s' % (
                self.targetexp.to_source(),
                self.vnameexp.to_source(),
                self.token,
                value)

        # The variable could be multi-line or have leading whitespace. For
        # regular variable assignment, whitespace after the token but before
        # the value is ignored. If we see leading whitespace in the value here,
        # the variable must have come from a define.
        if value.count('\n') > 0 or (len(value) and value[0].isspace()):
            # The parser holds the token in vnameexp for whatever reason.
            return '%sdefine %s\n%s\nendef' % (
                prefix,
                self.vnameexp.to_source(),
                value)

        return '%s%s %s %s' % (
                prefix,
                self.vnameexp.to_source(),
                self.token,
                value)

class Condition(object):
    """
    An abstract "condition", either ifeq or ifdef, perhaps negated.

    See https://www.gnu.org/software/make/manual/make.html#Conditional-Syntax

    Subclasses must implement:

    def evaluate(self, makefile)
    """

    def __eq__(self, other):
        raise Exception("%s must implement __eq__." % __class__)

    def __ne__(self, other):
        return not self.__eq__(other)

class EqCondition(Condition):
    """
    Represents an ifeq or ifneq conditional directive.

    This directive consists of two Expansions which are compared for equality.

    The `expected` field is a bool indicating what the condition must evaluate
    to in order for its body to be executed. If True, this is an "ifeq"
    conditional directive. If False, an "ifneq."
    """
    __slots__ = ('exp1', 'exp2', 'expected')

    def __init__(self, exp1, exp2):
        assert isinstance(exp1, (Expansion, StringExpansion))
        assert isinstance(exp2, (Expansion, StringExpansion))

        self.expected = True
        self.exp1 = exp1
        self.exp2 = exp2

    def evaluate(self, makefile):
        r1 = self.exp1.resolvestr(makefile, makefile.variables)
        r2 = self.exp2.resolvestr(makefile, makefile.variables)
        return (r1 == r2) == self.expected

    def __str__(self):
        return "ifeq (expected=%s) %s %s" % (self.expected, self.exp1, self.exp2)

    def __eq__(self, other):
        if not isinstance(other, EqCondition):
            return False

        return self.exp1 == other.exp1 \
                and self.exp2 == other.exp2 \
                and self.expected == other.expected

class IfdefCondition(Condition):
    """
    Represents an ifdef or ifndef conditional directive.

    This directive consists of a single expansion which represents the name of
    a variable (without the leading '$') which will be checked for definition.

    The `expected` field is a bool and has the same behavior as EqCondition.
    If it is True, this represents a "ifdef" conditional. If False, "ifndef."
    """
    __slots__ = ('exp', 'expected')

    def __init__(self, exp):
        assert isinstance(exp, (Expansion, StringExpansion))
        self.exp = exp
        self.expected = True

    def evaluate(self, makefile):
        vname = self.exp.resolvestr(makefile, makefile.variables)
        flavor, source, value = makefile.variables.get(vname, expand=False)

        if value is None:
            return not self.expected

        return (len(value) > 0) == self.expected

    def __str__(self):
        return "ifdef (expected=%s) %s" % (self.expected, self.exp)

    def __eq__(self, other):
        if not isinstance(other, IfdefCondition):
            return False

        return self.exp == other.exp and self.expected == other.expected

class ElseCondition(Condition):
    """
    Represents the transition between branches in a ConditionBlock.
    """
    __slots__ = ()

    def evaluate(self, makefile):
        return True

    def __str__(self):
        return "else"

    def __eq__(self, other):
        return isinstance(other, ElseCondition)

class ConditionBlock(Statement):
    """
    A set of related Conditions.

    This is essentially a list of 2-tuples of (Condition, list(Statement)).

    The parser creates a ConditionBlock for all statements related to the same
    conditional group. If iterating over the parser's output, where you think
    you would see an ifeq, you will see a ConditionBlock containing an IfEq. In
    other words, the parser collapses separate statements into this container
    class.

    ConditionBlock instances may exist within other ConditionBlock if the
    conditional logic is multiple levels deep.
    """
    __slots__ = ('loc', '_groups')

    def __init__(self, loc, condition):
        self.loc = loc
        self._groups = []
        self.addcondition(loc, condition)

    def getloc(self):
        return self.loc

    def addcondition(self, loc, condition):
        assert isinstance(condition, Condition)
        condition.loc = loc

        if len(self._groups) and isinstance(self._groups[-1][0], ElseCondition):
            raise errors.SyntaxError("Multiple else conditions for block starting at %s" % self.loc, loc)

        self._groups.append((condition, StatementList()))

    def append(self, statement):
        self._groups[-1][1].append(statement)

    def execute(self, makefile, context):
        i = 0
        for c, statements in self._groups:
            if c.evaluate(makefile):
                _data_log.debug("Condition at %s met by clause #%i", self.loc, i)
                statements.execute(makefile, context)
                return

            i += 1

    def dump(self, fd, indent):
        print("%sConditionBlock" % (indent,), file=fd)

        indent2 = indent + '  '
        for c, statements in self._groups:
            print("%s Condition %s" % (indent, c), file=fd)
            statements.dump(fd, indent2)
            print("%s ~Condition" % (indent,), file=fd)
        print("%s~ConditionBlock" % (indent,), file=fd)

    def to_source(self):
        lines = []
        index = 0
        for condition, statements in self:
            lines.append(ConditionBlock.condition_source(condition, index))
            index += 1

            for statement in statements:
                lines.append(statement.to_source())

        lines.append('endif')

        return '\n'.join(lines)

    def __eq__(self, other):
        if not isinstance(other, ConditionBlock):
            return False

        if len(self) != len(other):
            return False

        for i in range(0, len(self)):
            our_condition, our_statements = self[i]
            other_condition, other_statements = other[i]

            if our_condition != other_condition:
                return False

            if our_statements != other_statements:
                return False

        return True

    @staticmethod
    def condition_source(statement, index):
        """Convert a condition to its source representation.

        The index argument defines the index of this condition inside a
        ConditionBlock. If it is greater than 0, an "else" will be prepended
        to the result, if necessary.
        """
        prefix = ''
        if isinstance(statement, (EqCondition, IfdefCondition)) and index > 0:
            prefix = 'else '

        if isinstance(statement, IfdefCondition):
            s = statement.exp.s

            if statement.expected:
                return '%sifdef %s' % (prefix, s)

            return '%sifndef %s' % (prefix, s)

        if isinstance(statement, EqCondition):
            args = [
                statement.exp1.to_source(escape_comments=True),
                statement.exp2.to_source(escape_comments=True)]

            use_quotes = False
            single_quote_present = False
            double_quote_present = False
            for i, arg in enumerate(args):
                if len(arg) > 0 and (arg[0].isspace() or arg[-1].isspace()):
                    use_quotes = True

                    if "'" in arg:
                        single_quote_present = True

                    if '"' in arg:
                        double_quote_present = True

            # Quote everything if needed.
            if single_quote_present and double_quote_present:
                raise Exception('Cannot format condition with multiple quotes.')

            if use_quotes:
                for i, arg in enumerate(args):
                    # Double to single quotes.
                    if single_quote_present:
                        args[i] = '"' + arg + '"'
                    else:
                        args[i] = "'" + arg + "'"

            body = None
            if use_quotes:
                body = ' '.join(args)
            else:
                body = '(%s)' % ','.join(args)

            if statement.expected:
                return '%sifeq %s' % (prefix, body)

            return '%sifneq %s' % (prefix, body)

        if isinstance(statement, ElseCondition):
            return 'else'

        raise Exception('Unhandled Condition statement: %s' %
                statement.__class__)

    def __iter__(self):
        return iter(self._groups)

    def __len__(self):
        return len(self._groups)

    def __getitem__(self, i):
        return self._groups[i]

class Include(Statement):
    """
    Represents the include directive.

    See https://www.gnu.org/software/make/manual/make.html#Include

    The file to be included is represented by the Expansion defined in the
    field `exp`. `required` is a bool indicating whether execution should fail
    if the specified file could not be processed.
    """
    __slots__ = ('exp', 'required', 'deps')

    def __init__(self, exp, required, weak):
        assert isinstance(exp, (Expansion, StringExpansion))
        self.exp = exp
        self.required = required
        self.weak = weak

    def execute(self, makefile, context):
        files = self.exp.resolvesplit(makefile, makefile.variables)
        for f in files:
            makefile.include(f, self.required, loc=self.exp.loc, weak=self.weak)

    def dump(self, fd, indent):
        print("%sInclude %s" % (indent, self.exp), file=fd)

    def to_source(self):
        prefix = ''

        if not self.required:
            prefix = '-'

        return '%sinclude %s' % (prefix, self.exp.to_source())

    def __eq__(self, other):
        if not isinstance(other, Include):
            return False

        return self.exp == other.exp and self.required == other.required

class VPathDirective(Statement):
    """
    Represents the vpath directive.

    See https://www.gnu.org/software/make/manual/make.html#Selective-Search
    """
    __slots__ = ('exp',)

    def __init__(self, exp):
        assert isinstance(exp, (Expansion, StringExpansion))
        self.exp = exp

    def execute(self, makefile, context):
        words = list(stripdotslashes(self.exp.resolvesplit(makefile, makefile.variables)))
        if len(words) == 0:
            makefile.clearallvpaths()
        else:
            pattern = Pattern(words[0])
            mpaths = words[1:]

            if len(mpaths) == 0:
                makefile.clearvpath(pattern)
            else:
                dirs = []
                for mpath in mpaths:
                    dirs.extend((dir for dir in mpath.split(os.pathsep)
                                 if dir != ''))
                if len(dirs):
                    makefile.addvpath(pattern, dirs)

    def dump(self, fd, indent):
        print("%sVPath %s" % (indent, self.exp), file=fd)

    def to_source(self):
        return 'vpath %s' % self.exp.to_source()

    def __eq__(self, other):
        if not isinstance(other, VPathDirective):
            return False

        return self.exp == other.exp

class ExportDirective(Statement):
    """
    Represents the "export" directive.

    This is used to control exporting variables to sub makes.

    See https://www.gnu.org/software/make/manual/make.html#Variables_002fRecursion

    The `concurrent_set` field defines whether this statement occurred with or
    without a variable assignment. If False, no variable assignment was
    present. If True, the SetVariable immediately following this statement
    originally came from this export directive (the parser splits it into
    multiple statements).
    """

    __slots__ = ('exp', 'concurrent_set')

    def __init__(self, exp, concurrent_set):
        assert isinstance(exp, (Expansion, StringExpansion))
        self.exp = exp
        self.concurrent_set = concurrent_set

    def execute(self, makefile, context):
        if self.concurrent_set:
            vlist = [self.exp.resolvestr(makefile, makefile.variables)]
        else:
            vlist = list(self.exp.resolvesplit(makefile, makefile.variables))
            if not len(vlist):
                raise errors.DataError("Exporting all variables is not supported", self.exp.loc)

        for v in vlist:
            makefile.exportedvars[v] = True

    def dump(self, fd, indent):
        print("%sExport (single=%s) %s" % (indent, self.single, self.exp), file=fd)

    def to_source(self):
        return ('export %s' % self.exp.to_source()).rstrip()

    def __eq__(self, other):
        if not isinstance(other, ExportDirective):
            return False

        # single is irrelevant because it just says whether the next Statement
        # contains a variable definition.
        return self.exp == other.exp

class UnexportDirective(Statement):
    """
    Represents the "unexport" directive.

    This is the opposite of ExportDirective.
    """
    __slots__ = ('exp',)

    def __init__(self, exp):
        self.exp = exp

    def execute(self, makefile, context):
        vlist = list(self.exp.resolvesplit(makefile, makefile.variables))
        for v in vlist:
            makefile.exportedvars[v] = False

    def dump(self, fd, indent):
        print("%sUnexport %s" % (indent, self.exp), file=fd)

    def to_source(self):
        return 'unexport %s' % self.exp.to_source()

    def __eq__(self, other):
        if not isinstance(other, UnexportDirective):
            return False

        return self.exp == other.exp

class EmptyDirective(Statement):
    """
    Represents a standalone statement, usually an Expansion.

    You will encounter EmptyDirective instances if there is a function
    or similar at the top-level of a make file (e.g. outside of a rule or
    variable assignment). You can also find them as the bodies of
    ConditionBlock branches.
    """
    __slots__ = ('exp',)

    def __init__(self, exp):
        assert isinstance(exp, (Expansion, StringExpansion))
        self.exp = exp

    def execute(self, makefile, context):
        v = self.exp.resolvestr(makefile, makefile.variables)
        if v.strip() != '':
            raise errors.DataError("Line expands to non-empty value", self.exp.loc)

    def dump(self, fd, indent):
        print("%sEmptyDirective: %s" % (indent, self.exp), file=fd)

    def to_source(self):
        return self.exp.to_source()

    def __eq__(self, other):
        if not isinstance(other, EmptyDirective):
            return False

        return self.exp == other.exp

class _EvalContext(object):
    __slots__ = ('currule', 'weak')

    def __init__(self, weak):
        self.weak = weak

class StatementList(list):
    """
    A list of Statement instances.

    This is what is generated by the parser when a make file is parsed.

    Consumers can iterate over all Statement instances in this collection to
    statically inspect (and even modify) make files before they are executed.
    """
    __slots__ = ('mtime',)

    def append(self, statement):
        assert isinstance(statement, Statement)
        list.append(self, statement)

    def execute(self, makefile, context=None, weak=False):
        if context is None:
            context = _EvalContext(weak=weak)

        for s in self:
            s.execute(makefile, context)

    def dump(self, fd, indent):
        for s in self:
            s.dump(fd, indent)

    def __str__(self):
        fd = StringIO()
        self.dump(fd, '')
        return fd.getvalue()

    def to_source(self):
        return '\n'.join([s.to_source() for s in self])

def iterstatements(stmts):
    for s in stmts:
        yield s
        if isinstance(s, ConditionBlock):
            for c, sl in s:
                for s2 in iterstatments(sl): yield s2


"""
Functionality for parsing Makefile syntax.

Makefiles use a line-based parsing system. Continuations and substitutions are handled differently based on the
type of line being parsed:

Lines with makefile syntax condense continuations to a single space, no matter the actual trailing whitespace
of the first line or the leading whitespace of the continuation. In other situations, trailing whitespace is
relevant.

Lines with command syntax do not condense continuations: the backslash and newline are part of the command.
(GNU Make is buggy in this regard, at least on mac).

Lines with an initial tab are commands if they can be (there is a rule or a command immediately preceding).
Otherwise, they are parsed as makefile syntax.

This file parses into the parser data structures. Those classes are what actually
do the dirty work of "executing" the parsed data into a engine.Makefile.

Four iterator functions are available:
* iterdata
* itermakefilechars
* itercommandchars

The iterators handle line continuations and comments in different ways, but share a common calling
convention:

Called with (data, startoffset, tokenlist, finditer)

yield 4-tuples (flatstr, token, tokenoffset, afteroffset)
flatstr is data, guaranteed to have no tokens (may be '')
token, tokenoffset, afteroffset *may be None*. That means there is more text
coming.
"""

_pars_log = logging.getLogger('pymake.parser')

_skipws = re.compile('\S')
class Data(object):
    """
    A single virtual "line", which can be multiple source lines joined with
    continuations.
    """

    __slots__ = ('s', 'lstart', 'lend', 'loc')

    def __init__(self, s, lstart, lend, loc):
        self.s = s
        self.lstart = lstart
        self.lend = lend
        self.loc = loc

    @staticmethod
    def fromstring(s, path):
        return Data(s, 0, len(s), Location(path, 1, 0))

    def getloc(self, offset):
        assert offset >= self.lstart and offset <= self.lend
        return self.loc.offset(self.s, self.lstart, offset)

    def skipwhitespace(self, offset):
        """
        Return the offset of the first non-whitespace character in data starting at offset, or None if there are
        only whitespace characters remaining.
        """
        m = _skipws.search(self.s, offset, self.lend)
        if m is None:
            return self.lend

        return m.start(0)

_linere = re.compile(r'\\*\n')
def enumeratelines(s, filename):
    """
    Enumerate lines in a string as Data objects, joining line
    continuations.
    """

    off = 0
    lineno = 1
    curlines = 0
    for m in _linere.finditer(s):
        curlines += 1
        start, end = m.span(0)

        if (start - end) % 2 == 0:
            # odd number of backslashes is a continuation
            continue

        yield Data(s, off, end - 1, Location(filename, lineno, 0))

        lineno += curlines
        curlines = 0
        off = end

    yield Data(s, off, len(s), Location(filename, lineno, 0))

_alltokens = re.compile(r'''\\*\# | # hash mark preceeded by any number of backslashes
                            := |
                            \+= |
                            \?= |
                            :: |
                            (?:\$(?:$|[\(\{](?:%s)\s+|.)) | # dollar sign followed by EOF, a function keyword with whitespace, or any character
                            :(?![\\/]) | # colon followed by anything except a slash (Windows path detection)
                            [=#{}();,|'"]''' % '|'.join(functionmap.keys()), re.VERBOSE)

def iterdata(d, offset, tokenlist, it):
    """
    Iterate over flat data without line continuations, comments, or any special escaped characters.

    Typically used to parse recursively-expanded variables.
    """

    assert len(tokenlist), "Empty tokenlist passed to iterdata is meaningless!"
    assert offset >= d.lstart and offset <= d.lend, "offset %i should be between %i and %i" % (offset, d.lstart, d.lend)

    if offset == d.lend:
        return

    s = d.s
    for m in it:
        mstart, mend = m.span(0)
        token = s[mstart:mend]
        if token in tokenlist or (token[0] == '$' and '$' in tokenlist):
            yield s[offset:mstart], token, mstart, mend
        else:
            yield s[offset:mend], None, None, mend
        offset = mend

    yield s[offset:d.lend], None, None, None

# multiple backslashes before a newline are unescaped, halving their total number
_makecontinuations = re.compile(r'(?:\s*|((?:\\\\)+))\\\n\s*')
def _replacemakecontinuations(m):
    start, end = m.span(1)
    if start == -1:
        return ' '
    return ' '.rjust((end - start) // 2 + 1, '\\')

def itermakefilechars(d, offset, tokenlist, it, ignorecomments=False):
    """
    Iterate over data in makefile syntax. Comments are found at unescaped # characters, and escaped newlines
    are converted to single-space continuations.
    """

    assert offset >= d.lstart and offset <= d.lend, "offset %i should be between %i and %i" % (offset, d.lstart, d.lend)

    if offset == d.lend:
        return

    s = d.s
    for m in it:
        mstart, mend = m.span(0)
        token = s[mstart:mend]

        starttext = _makecontinuations.sub(_replacemakecontinuations, s[offset:mstart])

        if token[-1] == '#' and not ignorecomments:
            l = mend - mstart
            # multiple backslashes before a hash are unescaped, halving their total number
            if l % 2:
                # found a comment
                yield starttext + token[:(l - 1) // 2], None, None, None
                return
            else:
                yield starttext + token[-l // 2:], None, None, mend
        elif token in tokenlist or (token[0] == '$' and '$' in tokenlist):
            yield starttext, token, mstart, mend
        else:
            yield starttext + token, None, None, mend
        offset = mend

    yield _makecontinuations.sub(_replacemakecontinuations, s[offset:d.lend]), None, None, None

_findcomment = re.compile(r'\\*\#')
def flattenmakesyntax(d, offset):
    """
    A shortcut method for flattening line continuations and comments in makefile syntax without
    looking for other tokens.
    """

    assert offset >= d.lstart and offset <= d.lend, "offset %i should be between %i and %i" % (offset, d.lstart, d.lend)
    if offset == d.lend:
        return ''

    s = _makecontinuations.sub(_replacemakecontinuations, d.s[offset:d.lend])

    elements = []
    offset = 0
    for m in _findcomment.finditer(s):
        mstart, mend = m.span(0)
        elements.append(s[offset:mstart])
        if (mend - mstart) % 2:
            # even number of backslashes... it's a comment
            elements.append(''.ljust((mend - mstart - 1) // 2, '\\'))
            return ''.join(elements)

        # odd number of backslashes
        elements.append(''.ljust((mend - mstart - 2) // 2, '\\') + '#')
        offset = mend

    elements.append(s[offset:])
    return ''.join(elements)

def itercommandchars(d, offset, tokenlist, it):
    """
    Iterate over command syntax. # comment markers are not special, and escaped newlines are included
    in the output text.
    """

    assert offset >= d.lstart and offset <= d.lend, "offset %i should be between %i and %i" % (offset, d.lstart, d.lend)

    if offset == d.lend:
        return

    s = d.s
    for m in it:
        mstart, mend = m.span(0)
        token = s[mstart:mend]
        starttext = s[offset:mstart].replace('\n\t', '\n')

        if token in tokenlist or (token[0] == '$' and '$' in tokenlist):
            yield starttext, token, mstart, mend
        else:
            yield starttext + token, None, None, mend
        offset = mend

    yield s[offset:d.lend].replace('\n\t', '\n'), None, None, None

_redefines = re.compile('\s*define|\s*endef')
def iterdefinelines(it, startloc):
    """
    Process the insides of a define. Most characters are included literally. Escaped newlines are treated
    as they would be in makefile syntax. Internal define/endef pairs are ignored.
    """

    results = []

    definecount = 1
    for d in it:
        m = _redefines.match(d.s, d.lstart, d.lend)
        if m is not None:
            directive = m.group(0).strip()
            if directive == 'endef':
                definecount -= 1
                if definecount == 0:
                    return _makecontinuations.sub(_replacemakecontinuations, '\n'.join(results))
            else:
                definecount += 1

        results.append(d.s[d.lstart:d.lend])

    # Falling off the end is an unterminated define!
    raise errors.SyntaxError("define without matching endef", startloc)

def _ensureend(d, offset, msg):
    """
    Ensure that only whitespace remains in this data.
    """

    s = flattenmakesyntax(d, offset)
    if s != '' and not s.isspace():
        raise errors.SyntaxError(msg, d.getloc(offset))

_eqargstokenlist = ('(', "'", '"')

def ifeq(d, offset):
    if offset > d.lend - 1:
        raise errors.SyntaxError("No arguments after conditional", d.getloc(offset))

    # the variety of formats for this directive is rather maddening
    token = d.s[offset]
    if token not in _eqargstokenlist:
        raise errors.SyntaxError("No arguments after conditional", d.getloc(offset))

    offset += 1

    if token == '(':
        arg1, t, offset = parsemakesyntax(d, offset, (',',), itermakefilechars)
        if t is None:
            raise errors.SyntaxError("Expected two arguments in conditional", d.getloc(d.lend))

        arg1.rstrip()

        offset = d.skipwhitespace(offset)
        arg2, t, offset = parsemakesyntax(d, offset, (')',), itermakefilechars)
        if t is None:
            raise errors.SyntaxError("Unexpected text in conditional", d.getloc(offset))

        _ensureend(d, offset, "Unexpected text after conditional")
    else:
        arg1, t, offset = parsemakesyntax(d, offset, (token,), itermakefilechars)
        if t is None:
            raise errors.SyntaxError("Unexpected text in conditional", d.getloc(d.lend))

        offset = d.skipwhitespace(offset)
        if offset == d.lend:
            raise errors.SyntaxError("Expected two arguments in conditional", d.getloc(offset))

        token = d.s[offset]
        if token not in '\'"':
            raise errors.SyntaxError("Unexpected text in conditional", d.getloc(offset))

        arg2, t, offset = parsemakesyntax(d, offset + 1, (token,), itermakefilechars)

        _ensureend(d, offset, "Unexpected text after conditional")

    return EqCondition(arg1, arg2)

def ifneq(d, offset):
    c = ifeq(d, offset)
    c.expected = False
    return c

def ifdef(d, offset):
    e, t, offset = parsemakesyntax(d, offset, (), itermakefilechars)
    e.rstrip()

    return IfdefCondition(e)

def ifndef(d, offset):
    c = ifdef(d, offset)
    c.expected = False
    return c

_conditionkeywords = {
    'ifeq': ifeq,
    'ifneq': ifneq,
    'ifdef': ifdef,
    'ifndef': ifndef
    }

_conditiontokens = tuple(_conditionkeywords.keys())
_conditionre = re.compile(r'(%s)(?:$|\s+)' % '|'.join(_conditiontokens))

_directivestokenlist = _conditiontokens + \
    ('else', 'endif', 'define', 'endef', 'override', 'include', '-include', 'includedeps', '-includedeps', 'vpath', 'export', 'unexport')

_directivesre = re.compile(r'(%s)(?:$|\s+)' % '|'.join(_directivestokenlist))

_varsettokens = (':=', '+=', '?=', '=')

def _parsefile(pathname):
    fd = open(pathname, "rU")
    stmts = parsestring(fd.read(), pathname)
    stmts.mtime = os.fstat(fd.fileno()).st_mtime
    fd.close()
    return stmts

def _checktime(path, stmts):
    mtime = os.path.getmtime(path)
    if mtime != stmts.mtime:
        _pars_log.debug("Re-parsing makefile '%s': mtimes differ", path)
        return False

    return True

_parsecache = util.MostUsedCache(50, _parsefile, _checktime)

def parsefile(pathname):
    """
    Parse a filename into a StatementList. A cache is used to avoid re-parsing
    makefiles that have already been parsed and have not changed.
    """

    pathname = os.path.realpath(pathname)
    return _parsecache.get(pathname)

# colon followed by anything except a slash (Windows path detection)
_depfilesplitter = re.compile(r':(?![\\/])')
# simple variable references
_vars = re.compile('\$\((\w+)\)')

def parsedepfile(pathname):
    """
    Parse a filename listing only depencencies into a StatementList.
    Simple variable references are allowed in such files.
    """
    def continuation_iter(lines):
        current_line = []
        for line in lines:
            line = line.rstrip()
            if line.endswith("\\"):
                current_line.append(line.rstrip("\\"))
                continue
            if not len(line):
                continue
            current_line.append(line)
            yield ''.join(current_line)
            current_line = []
        if current_line:
            yield ''.join(current_line)

    def get_expansion(s):
        if '$' in s:
            expansion = Expansion()
            # for an input like e.g. "foo $(bar) baz",
            # _vars.split returns ["foo", "bar", "baz"]
            # every other element is a variable name.
            for i, element in enumerate(_vars.split(s)):
                if i % 2:
                    expansion.appendfunc(VariableRef(None,
                        StringExpansion(element, None)))
                elif element:
                    expansion.appendstr(element)

            return expansion

        return StringExpansion(s, None)

    pathname = os.path.realpath(pathname)
    stmts = StatementList()
    for line in continuation_iter(open(pathname).readlines()):
        target, deps = _depfilesplitter.split(line, 1)
        stmts.append(RuleStatement(get_expansion(target),
                                     get_expansion(deps), False))
    return stmts

def parsestring(s, filename):
    """
    Parse a string containing makefile data into a StatementList.
    """

    currule = False
    condstack = [StatementList()]

    fdlines = enumeratelines(s, filename)
    for d in fdlines:
        assert len(condstack) > 0

        offset = d.lstart

        if currule and offset < d.lend and d.s[offset] == '\t':
            e, token, offset = parsemakesyntax(d, offset + 1, (), itercommandchars)
            assert token is None
            assert offset is None
            condstack[-1].append(Command(e))
            continue

        # To parse Makefile syntax, we first strip leading whitespace and
        # look for initial keywords. If there are no keywords, it's either
        # setting a variable or writing a rule.

        offset = d.skipwhitespace(offset)
        if offset is None:
            continue

        m = _directivesre.match(d.s, offset, d.lend)
        if m is not None:
            kword = m.group(1)
            offset = m.end(0)

            if kword == 'endif':
                _ensureend(d, offset, "Unexpected data after 'endif' directive")
                if len(condstack) == 1:
                    raise errors.SyntaxError("unmatched 'endif' directive",
                                      d.getloc(offset))

                condstack.pop().endloc = d.getloc(offset)
                continue
            
            if kword == 'else':
                if len(condstack) == 1:
                    raise errors.SyntaxError("unmatched 'else' directive",
                                      d.getloc(offset))

                m = _conditionre.match(d.s, offset, d.lend)
                if m is None:
                    _ensureend(d, offset, "Unexpected data after 'else' directive.")
                    condstack[-1].addcondition(d.getloc(offset), ElseCondition())
                else:
                    kword = m.group(1)
                    if kword not in _conditionkeywords:
                        raise errors.SyntaxError("Unexpected condition after 'else' directive.",
                                          d.getloc(offset))

                    startoffset = offset
                    offset = d.skipwhitespace(m.end(1))
                    c = _conditionkeywords[kword](d, offset)
                    condstack[-1].addcondition(d.getloc(startoffset), c)
                continue

            if kword in _conditionkeywords:
                c = _conditionkeywords[kword](d, offset)
                cb = ConditionBlock(d.getloc(d.lstart), c)
                condstack[-1].append(cb)
                condstack.append(cb)
                continue

            if kword == 'endef':
                raise errors.SyntaxError("endef without matching define", d.getloc(offset))

            if kword == 'define':
                currule = False
                vname, t, i = parsemakesyntax(d, offset, (), itermakefilechars)
                vname.rstrip()

                startloc = d.getloc(d.lstart)
                value = iterdefinelines(fdlines, startloc)
                condstack[-1].append(SetVariable(vname, value=value, valueloc=startloc, token='=', targetexp=None))
                continue

            if kword in ('include', '-include', 'includedeps', '-includedeps'):
                if kword.startswith('-'):
                    required = False
                    kword = kword[1:]
                else:
                    required = True

                deps = kword == 'includedeps'

                currule = False
                incfile, t, offset = parsemakesyntax(d, offset, (), itermakefilechars)
                condstack[-1].append(Include(incfile, required, deps))

                continue

            if kword == 'vpath':
                currule = False
                e, t, offset = parsemakesyntax(d, offset, (), itermakefilechars)
                condstack[-1].append(VPathDirective(e))
                continue

            if kword == 'override':
                currule = False
                vname, token, offset = parsemakesyntax(d, offset, _varsettokens, itermakefilechars)
                vname.lstrip()
                vname.rstrip()

                if token is None:
                    raise errors.SyntaxError("Malformed override directive, need =", d.getloc(d.lstart))

                value = flattenmakesyntax(d, offset).lstrip()

                condstack[-1].append(SetVariable(vname, value=value, valueloc=d.getloc(offset), token=token, targetexp=None, source=Variables.SOURCE_OVERRIDE))
                continue

            if kword == 'export':
                currule = False
                e, token, offset = parsemakesyntax(d, offset, _varsettokens, itermakefilechars)
                e.lstrip()
                e.rstrip()

                if token is None:
                    condstack[-1].append(ExportDirective(e, concurrent_set=False))
                else:
                    condstack[-1].append(ExportDirective(e, concurrent_set=True))

                    value = flattenmakesyntax(d, offset).lstrip()
                    condstack[-1].append(SetVariable(e, value=value, valueloc=d.getloc(offset), token=token, targetexp=None))

                continue

            if kword == 'unexport':
                e, token, offset = parsemakesyntax(d, offset, (), itermakefilechars)
                condstack[-1].append(UnexportDirective(e))
                continue

        e, token, offset = parsemakesyntax(d, offset, _varsettokens + ('::', ':'), itermakefilechars)
        if token is None:
            e.rstrip()
            e.lstrip()
            if not e.isempty():
                condstack[-1].append(EmptyDirective(e))
            continue

        # if we encountered real makefile syntax, the current rule is over
        currule = False

        if token in _varsettokens:
            e.lstrip()
            e.rstrip()

            value = flattenmakesyntax(d, offset).lstrip()

            condstack[-1].append(SetVariable(e, value=value, valueloc=d.getloc(offset), token=token, targetexp=None))
        else:
            doublecolon = token == '::'

            # `e` is targets or target patterns, which can end up as
            # * a rule
            # * an implicit rule
            # * a static pattern rule
            # * a target-specific variable definition
            # * a pattern-specific variable definition
            # any of the rules may have order-only prerequisites
            # delimited by |, and a command delimited by ;
            targets = e

            e, token, offset = parsemakesyntax(d, offset,
                                               _varsettokens + (':', '|', ';'),
                                               itermakefilechars)
            if token in (None, ';'):
                condstack[-1].append(RuleStatement(targets, e, doublecolon))
                currule = True

                if token == ';':
                    offset = d.skipwhitespace(offset)
                    e, t, offset = parsemakesyntax(d, offset, (), itercommandchars)
                    condstack[-1].append(Command(e))

            elif token in _varsettokens:
                e.lstrip()
                e.rstrip()

                value = flattenmakesyntax(d, offset).lstrip()
                condstack[-1].append(SetVariable(e, value=value, valueloc=d.getloc(offset), token=token, targetexp=targets))
            elif token == '|':
                raise errors.SyntaxError('order-only prerequisites not implemented', d.getloc(offset))
            else:
                assert token == ':'
                # static pattern rule

                pattern = e

                deps, token, offset = parsemakesyntax(d, offset, (';',), itermakefilechars)

                condstack[-1].append(StaticPatternRule(targets, pattern, deps, doublecolon))
                currule = True

                if token == ';':
                    offset = d.skipwhitespace(offset)
                    e, token, offset = parsemakesyntax(d, offset, (), itercommandchars)
                    condstack[-1].append(Command(e))

    if len(condstack) != 1:
        raise errors.SyntaxError("Condition never terminated with endif", condstack[-1].loc)

    return condstack[0]

_PARSESTATE_TOPLEVEL = 0    # at the top level
_PARSESTATE_FUNCTION = 1    # expanding a function call
_PARSESTATE_VARNAME = 2     # expanding a variable expansion.
_PARSESTATE_SUBSTFROM = 3   # expanding a variable expansion substitution "from" value
_PARSESTATE_SUBSTTO = 4     # expanding a variable expansion substitution "to" value
_PARSESTATE_PARENMATCH = 5  # inside nested parentheses/braces that must be matched

class ParseStackFrame(object):
    __slots__ = ('parsestate', 'parent', 'expansion', 'tokenlist', 'openbrace', 'closebrace', 'function', 'loc', 'varname', 'substfrom')

    def __init__(self, parsestate, parent, expansion, tokenlist, openbrace, closebrace, function=None, loc=None):
        self.parsestate = parsestate
        self.parent = parent
        self.expansion = expansion
        self.tokenlist = tokenlist
        self.openbrace = openbrace
        self.closebrace = closebrace
        self.function = function
        self.loc = loc

    def __str__(self):
        return "<state=%i expansion=%s tokenlist=%s openbrace=%s closebrace=%s>" % (self.parsestate, self.expansion, self.tokenlist, self.openbrace, self.closebrace)

_matchingbrace = {
    '(': ')',
    '{': '}',
    }

def parsemakesyntax(d, offset, stopon, iterfunc):
    """
    Given Data, parse it into a engine.Expansion.

    @param stopon (sequence)
        Indicate characters where toplevel parsing should stop.

    @param iterfunc (generator function)
        A function which is used to iterate over d, yielding (char, offset, loc)
        @see iterdata
        @see itermakefilechars
        @see itercommandchars
 
    @return a tuple (expansion, token, offset). If all the data is consumed,
    token and offset will be None
    """

    assert callable(iterfunc)

    stacktop = ParseStackFrame(_PARSESTATE_TOPLEVEL, None, Expansion(loc=d.getloc(d.lstart)),
                               tokenlist=stopon + ('$',),
                               openbrace=None, closebrace=None)

    tokeniterator = _alltokens.finditer(d.s, offset, d.lend)

    di = iterfunc(d, offset, stacktop.tokenlist, tokeniterator)
    while True: # this is not a for loop because `di` changes during the function
        assert stacktop is not None
        try:
            s, token, tokenoffset, offset = next(di)
        except StopIteration:
            break

        stacktop.expansion.appendstr(s)
        if token is None:
            continue

        parsestate = stacktop.parsestate

        if token[0] == '$':
            if tokenoffset + 1 == d.lend:
                # an unterminated $ expands to nothing
                break

            loc = d.getloc(tokenoffset)
            c = token[1]
            if c == '$':
                assert len(token) == 2
                stacktop.expansion.appendstr('$')
            elif c in ('(', '{'):
                closebrace = _matchingbrace[c]

                if len(token) > 2:
                    fname = token[2:].rstrip()
                    fn = functionmap[fname](loc)
                    e = Expansion()
                    if len(fn) + 1 == fn.maxargs:
                        tokenlist = (c, closebrace, '$')
                    else:
                        tokenlist = (',', c, closebrace, '$')

                    stacktop = ParseStackFrame(_PARSESTATE_FUNCTION, stacktop,
                                               e, tokenlist, function=fn,
                                               openbrace=c, closebrace=closebrace)
                else:
                    e = Expansion()
                    tokenlist = (':', c, closebrace, '$')
                    stacktop = ParseStackFrame(_PARSESTATE_VARNAME, stacktop,
                                               e, tokenlist,
                                               openbrace=c, closebrace=closebrace, loc=loc)
            else:
                assert len(token) == 2
                e = Expansion.fromstring(c, loc)
                stacktop.expansion.appendfunc(VariableRef(loc, e))
        elif token in ('(', '{'):
            assert token == stacktop.openbrace

            stacktop.expansion.appendstr(token)
            stacktop = ParseStackFrame(_PARSESTATE_PARENMATCH, stacktop,
                                       stacktop.expansion,
                                       (token, stacktop.closebrace, '$'),
                                       openbrace=token, closebrace=stacktop.closebrace, loc=d.getloc(tokenoffset))
        elif parsestate == _PARSESTATE_PARENMATCH:
            assert token == stacktop.closebrace
            stacktop.expansion.appendstr(token)
            stacktop = stacktop.parent
        elif parsestate == _PARSESTATE_TOPLEVEL:
            assert stacktop.parent is None
            return stacktop.expansion.finish(), token, offset
        elif parsestate == _PARSESTATE_FUNCTION:
            if token == ',':
                stacktop.function.append(stacktop.expansion.finish())

                stacktop.expansion = Expansion()
                if len(stacktop.function) + 1 == stacktop.function.maxargs:
                    tokenlist = (stacktop.openbrace, stacktop.closebrace, '$')
                    stacktop.tokenlist = tokenlist
            elif token in (')', '}'):
                fn = stacktop.function
                fn.append(stacktop.expansion.finish())
                fn.setup()
                
                stacktop = stacktop.parent
                stacktop.expansion.appendfunc(fn)
            else:
                assert False, "Not reached, _PARSESTATE_FUNCTION"
        elif parsestate == _PARSESTATE_VARNAME:
            if token == ':':
                stacktop.varname = stacktop.expansion
                stacktop.parsestate = _PARSESTATE_SUBSTFROM
                stacktop.expansion = Expansion()
                stacktop.tokenlist = ('=', stacktop.openbrace, stacktop.closebrace, '$')
            elif token in (')', '}'):
                fn = VariableRef(stacktop.loc, stacktop.expansion.finish())
                stacktop = stacktop.parent
                stacktop.expansion.appendfunc(fn)
            else:
                assert False, "Not reached, _PARSESTATE_VARNAME"
        elif parsestate == _PARSESTATE_SUBSTFROM:
            if token == '=':
                stacktop.substfrom = stacktop.expansion
                stacktop.parsestate = _PARSESTATE_SUBSTTO
                stacktop.expansion = Expansion()
                stacktop.tokenlist = (stacktop.openbrace, stacktop.closebrace, '$')
            elif token in (')', '}'):
                # A substitution of the form $(VARNAME:.ee) is probably a mistake, but make
                # parses it. Issue a warning. Combine the varname and substfrom expansions to
                # make the compatible varname. See tests/var-substitutions.mk SIMPLE3SUBSTNAME
                _pars_log.warning("%s: Variable reference looks like substitution without =", stacktop.loc)
                stacktop.varname.appendstr(':')
                stacktop.varname.concat(stacktop.expansion)
                fn = VariableRef(stacktop.loc, stacktop.varname.finish())
                stacktop = stacktop.parent
                stacktop.expansion.appendfunc(fn)
            else:
                assert False, "Not reached, _PARSESTATE_SUBSTFROM"
        elif parsestate == _PARSESTATE_SUBSTTO:
            assert token in  (')','}'), "Not reached, _PARSESTATE_SUBSTTO"

            fn = SubstitutionRef(stacktop.loc, stacktop.varname.finish(),
                                 stacktop.substfrom.finish(), stacktop.expansion.finish())
            stacktop = stacktop.parent
            stacktop.expansion.appendfunc(fn)
        else:
            assert False, "Unexpected parse state %s" % stacktop.parsestate

        if stacktop.parent is not None and iterfunc == itercommandchars:
            di = itermakefilechars(d, offset, stacktop.tokenlist, tokeniterator,
                                   ignorecomments=True)
        else:
            di = iterfunc(d, offset, stacktop.tokenlist, tokeniterator)

    if stacktop.parent is not None:
        raise errors.SyntaxError("Unterminated function call", d.getloc(offset))

    assert stacktop.parsestate == _PARSESTATE_TOPLEVEL

    return stacktop.expansion.finish(), None, None
