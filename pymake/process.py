"""
Skipping shell invocations is good, when possible. This wrapper around subprocess does dirty work of
parsing command lines into argv and making sure that no shell magic is being used.
"""
from __future__ import print_function

import re, logging, sys, traceback, os, glob

import command, util
if sys.platform=='win32':
    import win32process

_log = logging.getLogger('pymake.process')

_escapednewlines = re.compile(r'\\\n')

def tokens2re(tokens):
    # Create a pattern for non-escaped tokens, in the form:
    #   (?<!\\)(?:a|b|c...)
    # This is meant to match patterns a, b, or c, or ... if they are not
    # preceded by a backslash.
    # where a, b, c... are in the form
    #   (?P<name>pattern)
    # which matches the pattern and captures it in a named match group.
    # The group names and patterns come are given as a dict in the function
    # argument.
    nonescaped = r'(?<!\\)(?:%s)' % '|'.join('(?P<%s>%s)' % (name, value) for name, value in tokens.items())
    # The final pattern matches either the above pattern, or an escaped
    # backslash, captured in the "escape" match group.
    return re.compile('(?:%s|%s)' % (nonescaped, r'(?P<escape>\\\\)'))

_unquoted_tokens = tokens2re({
  'whitespace': r'[\t\r\n ]+',
  'quote': r'[\'"]',
  'comment': '#',
  'special': r'[<>&|`~(){}$;]',
  'backslashed': r'\\[^\\]',
  'glob': r'[\*\?]',
})

_doubly_quoted_tokens = tokens2re({
  'quote': '"',
  'backslashedquote': r'\\"',
  'special': '\$',
  'backslashed': r'\\[^\\"]',
})

class MetaCharacterException(Exception):
    def __init__(self, char):
        self.char = char

class ClineSplitter(list):
    """
    Parses a given command line string and creates a list of command
    and arguments, with wildcard expansion.
    """
    def __init__(self, cline, cwd):
        self.cwd = cwd
        self.arg = None
        self.cline = cline
        self.glob = False
        self._parse_unquoted()

    def _push(self, str):
        """
        Push the given string as part of the current argument
        """
        if self.arg is None:
            self.arg = ''
        self.arg += str

    def _next(self):
        """
        Finalize current argument, effectively adding it to the list.
        Perform globbing if needed.
        """
        if self.arg is None:
            return
        if self.glob:
            if os.path.isabs(self.arg):
                path = self.arg
            else:
                path = os.path.join(self.cwd, self.arg)
            globbed = glob.glob(path)
            if not globbed:
                # If globbing doesn't find anything, the literal string is
                # used.
                self.append(self.arg)
            else:
                self.extend(f[len(path)-len(self.arg):] for f in globbed)
            self.glob = False
        else:
            self.append(self.arg)
        self.arg = None

    def _parse_unquoted(self):
        """
        Parse command line remainder in the context of an unquoted string.
        """
        while self.cline:
            # Find the next token
            m = _unquoted_tokens.search(self.cline)
            # If we find none, the remainder of the string can be pushed to
            # the current argument and the argument finalized
            if not m:
                self._push(self.cline)
                break
            # The beginning of the string, up to the found token, is part of
            # the current argument
            if m.start():
                self._push(self.cline[:m.start()])
            self.cline = self.cline[m.end():]

            match = dict([(name, value) for name, value in m.groupdict().items() if value])
            if 'quote' in match:
                # " or ' start a quoted string
                if match['quote'] == '"':
                    self._parse_doubly_quoted()
                else:
                    self._parse_quoted()
            elif 'comment' in match:
                # Comments are ignored. The current argument can be finalized,
                # and parsing stopped.
                break
            elif 'special' in match:
                # Unquoted, non-escaped special characters need to be sent to a
                # shell.
                raise MetaCharacterException(match['special'])
            elif 'whitespace' in match:
                # Whitespaces terminate current argument.
                self._next()
            elif 'escape' in match:
                # Escaped backslashes turn into a single backslash
                self._push('\\')
            elif 'backslashed' in match:
                # Backslashed characters are unbackslashed
                # e.g. echo \a -> a
                self._push(match['backslashed'][1])
            elif 'glob' in match:
                # ? or * will need globbing
                self.glob = True
                self._push(m.group(0))
            else:
                raise Exception("Shouldn't reach here")
        if self.arg:
            self._next()

    def _parse_quoted(self):
        # Single quoted strings are preserved, except for the final quote
        index = self.cline.find("'")
        if index == -1:
            raise Exception('Unterminated quoted string in command')
        self._push(self.cline[:index])
        self.cline = self.cline[index+1:]

    def _parse_doubly_quoted(self):
        if not self.cline:
            raise Exception('Unterminated quoted string in command')
        while self.cline:
            m = _doubly_quoted_tokens.search(self.cline)
            if not m:
                raise Exception('Unterminated quoted string in command')
            self._push(self.cline[:m.start()])
            self.cline = self.cline[m.end():]
            match = dict([(name, value) for name, value in m.groupdict().items() if value])
            if 'quote' in match:
                # a double quote ends the quoted string, so go back to
                # unquoted parsing
                return
            elif 'special' in match:
                # Unquoted, non-escaped special characters in a doubly quoted
                # string still have a special meaning and need to be sent to a
                # shell.
                raise MetaCharacterException(match['special'])
            elif 'escape' in match:
                # Escaped backslashes turn into a single backslash
                self._push('\\')
            elif 'backslashedquote' in match:
                # Backslashed double quotes are un-backslashed
                self._push('"')
            elif 'backslashed' in match:
                # Backslashed characters are kept backslashed
                self._push(match['backslashed'])

def clinetoargv(cline, cwd):
    """
    If this command line can safely skip the shell, return an argv array.
    @returns argv, badchar
    """
    str = _escapednewlines.sub('', cline)
    try:
        args = ClineSplitter(str, cwd)
    except MetaCharacterException as e:
        return None, e.char

    if len(args) and args[0].find('=') != -1:
        return None, '='

    return args, None

# shellwords contains a set of shell builtin commands that need to be
# executed within a shell. It also contains a set of commands that are known
# to be giving problems when run directly instead of through the msys shell.
shellwords = (':', '.', 'break', 'cd', 'continue', 'exec', 'exit', 'export',
              'getopts', 'hash', 'pwd', 'readonly', 'return', 'shift', 
              'test', 'times', 'trap', 'umask', 'unset', 'alias',
              'set', 'bind', 'builtin', 'caller', 'command', 'declare',
              'echo', 'enable', 'help', 'let', 'local', 'logout', 
              'printf', 'read', 'shopt', 'source', 'type', 'typeset',
              'ulimit', 'unalias', 'set', 'find')

def prepare_command(cline, cwd, loc):
    """
    Returns a list of command and arguments for the given command line string.
    If the command needs to be run through a shell for some reason, the
    returned list contains the shell invocation.
    """

    #TODO: call this once up-front somewhere and save the result?
    shell, msys = util.checkmsyscompat()

    shellreason = None
    executable = None
    if msys and cline.startswith('/'):
        shellreason = "command starts with /"
    else:
        argv, badchar = clinetoargv(cline, cwd)
        if argv is None:
            shellreason = "command contains shell-special character '%s'" % (badchar,)
        elif len(argv) and argv[0] in shellwords:
            shellreason = "command starts with shell primitive '%s'" % (argv[0],)
        elif argv and (os.sep in argv[0] or os.altsep and os.altsep in argv[0]):
            executable = util.normaljoin(cwd, argv[0])
            # Avoid "%1 is not a valid Win32 application" errors, assuming
            # that if the executable path is to be resolved with PATH, it will
            # be a Win32 executable.
            if sys.platform == 'win32' and os.path.isfile(executable) and open(executable, 'rb').read(2) == "#!":
                shellreason = "command executable starts with a hashbang"

    if shellreason is not None:
        _log.debug("%s: using shell: %s: '%s'", loc, shellreason, cline)
        if msys:
            if len(cline) > 3 and cline[1] == ':' and cline[2] == '/':
                cline = '/' + cline[0] + cline[2:]
        argv = [shell, "-c", cline]
        executable = None

    return executable, argv

def call(cline, env, cwd, loc, cb, context, echo, justprint=False):
    executable, argv = prepare_command(cline, cwd, loc)

    if not len(argv):
        cb(res=0)
        return

    if argv[0] == command.makepypath:
        command.main(argv[1:], env, cwd, cb)
        return

    if argv[0:2] == [sys.executable.replace('\\', '/'),
                     command.makepypath.replace('\\', '/')]:
        command.main(argv[2:], env, cwd, cb)
        return

    context.call(argv, executable=executable, shell=False, env=env, cwd=cwd, cb=cb,
                 echo=echo, justprint=justprint)

def call_native(module, method, argv, env, cwd, loc, cb, context, echo, justprint=False,
                pycommandpath=None):
    context.call_native(module, method, argv, env=env, cwd=cwd, cb=cb,
                        echo=echo, justprint=justprint, pycommandpath=pycommandpath)

def statustoresult(status):
    """
    Convert the status returned from waitpid into a prettier numeric result.
    """
    sig = status & 0xFF
    if sig:
        return -sig

    return status >>8
