from predicates.prenex import *

# f, p = uniquely_rename_quantified_variables(Formula.parse("Ax[x=x]"))
# print(f)
# print(p)
f, p = pull_out_quantifications_from_right_across_binary_operator(Formula.parse("(S()&Az[Ew[z=w]])"))

print(p.is_valid())
print(f)