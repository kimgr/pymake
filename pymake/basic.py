"""
Basic type definitions. Do not introduce dependencies to other pymake modules,
or you risk circular dependencies.
"""
import re


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
