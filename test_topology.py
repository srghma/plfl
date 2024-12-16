# sage -python test_topology.py

import unittest
from topology import *
from sage.symbolic.all import SR
from sage.rings.integer import Integer


class TestTopologyFunctions(unittest.TestCase):

    def test_contains_empty_set(self):
        self.assertTrue(contains_empty_set([Set([Set()])]))
        self.assertFalse(contains_empty_set([Set([Set(1)])]))
        self.assertTrue(contains_empty_set([Set([Set()], [Set(1)])]))

    def test_contains_parent_set(self):
        self.assertTrue(contains_parent_set([1, 2], [Set(s) for s in [[], [1, 2]]]))
        self.assertFalse(contains_parent_set([1, 2], [Set(s) for s in [[], [1]]]))
        self.assertTrue(contains_parent_set([1], [Set(s) for s in [[], [1]]]))

    def test_closed_under_unions(self):
        self.assertTrue(closed_under_unions([1, 2], [Set(s) for s in [[], [1, 2]]]))
        self.assertTrue(closed_under_unions([1, 2], [Set(s) for s in [[], [1], [2], [1, 2]]]))
        self.assertFalse(closed_under_unions([1, 2], [Set(s) for s in [[], [1]]]))

    def test_closed_under_intersections(self):
         self.assertTrue(closed_under_intersections([1, 2], [Set(s) for s in [[], [1, 2]]]))
         self.assertTrue(closed_under_intersections([1, 2], [Set(s) for s in [[], [1], [2], [1, 2]]]))
         self.assertFalse(closed_under_intersections([1, 2], [Set(s) for s in [[], [1]]]))
         self.assertFalse(closed_under_intersections([1, 2], [Set(s) for s in [[1]]]))

    def test_is_valid_topology_space(self):
        self.assertFalse(is_valid_topology_space([1, 2], [Set(s) for s in [[]]]))
        self.assertTrue(is_valid_topology_space([1, 2], [Set(s) for s in [[], [1, 2]]]))
        self.assertTrue(is_valid_topology_space([1, 2], [Set(s) for s in [[], [1], [2], [1, 2]]]))
        self.assertFalse(is_valid_topology_space([1, 2], [Set(s) for s in [[], [1]]]))
        self.assertFalse(is_valid_topology_space([1, 2], [Set(s) for s in [[], [1], [2]]]))
        self.assertTrue(is_valid_topology_space([1, 2], [Set(s) for s in [[], [1], [1, 2]]]))
        self.assertFalse(is_valid_topology_space([1, 2], [Set(s) for s in [[1]]]))
        self.assertFalse(is_valid_topology_space([1, 2], [Set(s) for s in [[], [1], [2],[]]]))


    def test_is_hausdorff(self):
        a, b, c = SR.var('a'), SR.var('b'), SR.var('c')
        self.assertTrue(is_hausdorff([Integer(1), Integer(2)], [Set([Integer(1)]), Set([Integer(2)]), Set([Integer(1), Integer(2)])]))
        self.assertTrue(is_hausdorff([Integer(1), Integer(2)], [Set([]), Set([Integer(1)]), Set([Integer(2)]), Set([Integer(1), Integer(2)])]))
        self.assertFalse(is_hausdorff([Integer(1), Integer(2)], [Set([]), Set([Integer(1), Integer(2)])]))
        self.assertTrue(is_hausdorff([a, b, c], [Set([a]), Set([b]), Set([c]), Set([a, b]), Set([b, c]), Set([a, b, c]), Set([])]))
        self.assertTrue(is_hausdorff([Integer(1),Integer(2)],[Set([]), Set([Integer(1)]),Set([Integer(1),Integer(2)])]))
        self.assertFalse(is_hausdorff([Integer(1),Integer(2),Integer(3)], [Set([]),Set([Integer(1),Integer(2),Integer(3)])]))


if __name__ == '__main__':
    unittest.main()
