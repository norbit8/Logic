from predicates.syntax import *
from propositions.axiomatic_systems import *

# from predicates.proofs import *
# from predicates.functions import *
from propositions.tautology import prove_tautology as Pprove_tautology
from predicates.proofs import *

formula = Formula.parse('(R(c)->R(c))')
skeleton = PropositionalFormula.parse('(z23->z23)')
skeleton_proof = Pprove_tautology(skeleton)
print(skeleton_proof)
proof = prove_from_skeleton_proof(formula, skeleton_proof, frozendict({'z23':Formula.parse('R(c)')}))

# assert proof.assumptions == PROPOSITIONAL_AXIOMATIC_SYSTEM_SCHEMAS
# assert proof.conclusion == formula
# assert proof.is_valid()