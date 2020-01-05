from predicates.prover import *
from predicates.syntax import *

prover = Prover({'Ay[(Man(y)->Mortal(y))]', 'Man(aristotle)'}, False)
step1 = prover.add_assumption('Ay[(Man(y)->Mortal(y))]')
step2 = prover.add_universal_instantiation(
    '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
# step3 = prover.add_assumption('Man(aristotle)')
# step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
# proof = prover.qed()

# print(prover.qed())

# print(Prover.helper([Formula.parse("x=x"), Formula.parse("Ay[x=x]"), Formula.parse("(R(x)->R(f(x)))")]))