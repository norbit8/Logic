from predicates.syntax import *
from predicates.functions import *

f = Formula.parse("GT(f(a),g(b))")

# p = Term.parse("r(f(h(x)),g(x))")

# p1 = compile_term(f.arguments[0])
# p2 = compile_term(f.arguments[1])
# print(p1)
# print(p2)
# print(compile_term(p))
# print(replace_equality(compile_term(p)))


print(replace_functions_with_relations_in_formula(f))