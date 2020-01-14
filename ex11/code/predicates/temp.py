from predicates.prenex import *

# f, p = uniquely_rename_quantified_variables(Formula.parse("Ax[x=x]"))
# print(f)
# print(p)
formula = Formula.parse('~~Ax[R()]')
print("OUR FORMULA", formula)
returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(formula)
print(proof)
print(returned_formula)