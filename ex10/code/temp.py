from predicates.semantics import *

from  typing import Set,List


import itertools

pairs = {('a', 'a'), ('a', 'b'), ('b', 'a')}
model = Model({'a', 'b'}, {'bob': 'a'}, {'Friends': pairs})
f0 = Formula.parse('Friends(bob,bob)')
f1 = Formula.parse('Friends(bob,y)')
f2 = Formula.parse('Friends(x,bob)')
f3 = Formula.parse('Friends(x,y)')

f0 = Formula.parse('Friends(bob,bob)')
f1 = Formula.parse('Friends(bob,y)')
f2 = Formula.parse('Friends(x,bob)')
f3 = Formula.parse('Friends(x,y)')

pairs = {('a', 'a'), ('a', 'b'), ('b', 'a')}
model = Model({'a', 'b'}, {'bob': 'a'}, {'Friends': pairs})
f0 = Formula.parse('Friends(bob,bob)')
f1 = Formula.parse('Friends(bob,y)')
f2 = Formula.parse('Friends(x,bob)')
f3 = Formula.parse('Friends(x,y)')

formula = Formula.parse('(F(z,a)->z=b)')
model = Model({'a', 'b'}, {'a': 'a', 'b': 'b'},
              {'F': {('a', 'a'), ('b', 'b')}})

result = model.is_model_of(frozenset({formula}))
assert not result

