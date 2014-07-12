import unittest

import pymake.engine

class VariableRefTest(unittest.TestCase):
    def test_get_expansions(self):
        e = pymake.engine.StringExpansion('FOO', None)
        f = pymake.engine.VariableRef(None, e)

        exps = list(f.expansions())
        self.assertEqual(len(exps), 1)

class GetExpansionsTest(unittest.TestCase):
    def test_get_arguments(self):
        f = pymake.engine.SubstFunction(None)

        e1 = pymake.engine.StringExpansion('FOO', None)
        e2 = pymake.engine.StringExpansion('BAR', None)
        e3 = pymake.engine.StringExpansion('BAZ', None)

        f.append(e1)
        f.append(e2)
        f.append(e3)

        exps = list(f.expansions())
        self.assertEqual(len(exps), 3)

    def test_descend(self):
        f = pymake.engine.StripFunction(None)

        e = pymake.engine.Expansion(None)

        e1 = pymake.engine.StringExpansion('FOO', None)
        f1 = pymake.engine.VariableRef(None, e1)
        e.appendfunc(f1)

        f2 = pymake.engine.WildcardFunction(None)
        e2 = pymake.engine.StringExpansion('foo/*', None)
        f2.append(e2)
        e.appendfunc(f2)

        f.append(e)

        exps = list(f.expansions())
        self.assertEqual(len(exps), 1)

        exps = list(f.expansions(True))
        self.assertEqual(len(exps), 3)

        self.assertFalse(f.is_filesystem_dependent)

if __name__ == '__main__':
    unittest.main()
