from sage.sets.all import *
from sage.misc.functional import *
from itertools import combinations
from sage.symbolic.all import SR

# Function to check if a set contains the empty set
def contains_empty_set(topology_space):
    return Set([]) in topology_space

# Function to check if a topology contains the parent set
def contains_parent_set(parent_set, topology_space):
    return Set(parent_set) in topology_space

# Function to check if a topology is closed under arbitrary unions
def closed_under_unions(parent_set, topology_space):

    if not topology_space:
      return False

    unions = []
    for i in range(len(topology_space)):
      for j in range(len(topology_space)):
        unions.append(topology_space[i].union(topology_space[j]))


    all_in_topology = all(union in topology_space for union in unions)

    return all_in_topology and Set(parent_set) in topology_space

# Function to check if a topology is closed under finite intersections
def closed_under_intersections(parent_set, topology_space):

    if not topology_space:
        return False


    for subset in powerset(topology_space):
      if not subset:
        if not Set(parent_set) in topology_space:
          return False
      else:
        intersection = subset[0]
        for s in subset[1:]:
          intersection = intersection.intersection(s)
        if not intersection in topology_space:
          return False

    return Set(parent_set) in topology_space

# Function to check if a topology is valid
def is_valid_topology_space(parent_set, topology_space):
    return (contains_empty_set(topology_space) and
            contains_parent_set(parent_set, topology_space) and
            closed_under_unions(parent_set, topology_space) and
            closed_under_intersections(parent_set, topology_space))


# Function to check if a topology is Hausdorff
def is_hausdorff(parent_set, topology):

    if not contains_parent_set(parent_set,topology) or not contains_empty_set(topology):
        return False

    for point_pair in combinations(parent_set, 2):
        x, y = point_pair
        # Check if the value of a variable is in an open set.
        open_sets_x = [s for s in topology if any(el == x for el in s)]
        open_sets_y = [s for s in topology if any(el == y for el in s)]

        found_disjoint = False
        for u in open_sets_x:
            for v in open_sets_y:
              if u != v and u.intersection(v) == Set([]):
                  found_disjoint = True
                  break
            if found_disjoint:
                break
        if not found_disjoint:
            return False
    return True

# Generate the power set of a given set
def powerset(s):
    s = list(s)
    return [Set(subset) for i in range(len(s) + 1) for subset in combinations(s, i)]
