# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """        
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1
    prover = Prover([x for x in proof.assumptions if x.formula != assumption])
    line_mapper = dict()
    for index_line, line in enumerate(proof.lines):
        if isinstance(line, Proof.AssumptionLine):
            if line.formula == assumption:
                line_number = prover.add_tautology(Formula('->', assumption, assumption))
                line_mapper[index_line] = line_number
            else:
                luther = prover.add_instantiated_assumption(line.formula, line.assumption, line.instantiation_map)
                step_father = prover.add_tautology(Formula('->', line.formula, Formula('->', assumption, line.formula)))
                line_number = prover.add_mp(Formula('->', assumption, line.formula), luther, step_father)
                line_mapper[index_line] = line_number
        if isinstance(line, Proof.MPLine):
            real_antecedent = line_mapper[line.antecedent_line_number]
            real_conditional = line_mapper[line.conditional_line_number]
            line_number = prover.add_tautological_implication(Formula('->', assumption, line.formula),
                                                {real_antecedent, real_conditional})
            line_mapper[index_line] = line_number
        if isinstance(line, Proof.UGLine):
            phi = assumption
            psi = line.formula.predicate
            partA = Formula('A', line.formula.variable, Formula('->', phi, psi))
            partB = Formula('->', partA ,Formula('->', phi, line.formula))
            line_conditional = prover.add_instantiated_assumption(partB, Prover.US,
                                                             {'x': line.formula.variable,
                                                              'Q': phi,
                                                              'R': psi.substitute({line.formula.variable: Term.parse("_")})})
            antecedent_number = prover.add_ug(Formula('A',
                                             line.formula.variable, Formula('->', phi, psi)),
                                             line_mapper[line.predicate_line_number])
            line_number = prover.add_mp(Formula('->', phi, line.formula), antecedent_number, line_conditional)
            line_mapper[index_line] = line_number
        if isinstance(line, Proof.TautologyLine):
            luther = prover.add_tautology(line.formula)
            step_father = prover.add_tautology(Formula('->', line.formula, Formula('->', assumption, line.formula)))
            line_number = prover.add_mp(Formula('->', assumption, line.formula), luther, step_father)
            line_mapper[index_line] = line_number
    return prover.qed()


def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2
    removed_proof = remove_assumption(proof, assumption)
    contradiction = proof.conclusion
    prover = Prover(removed_proof.assumptions, print_as_proof_forms)
    step1 = prover.add_proof(removed_proof.conclusion, removed_proof)
    conse = prover.add_tautological_implication(Formula.parse(f"(~{contradiction}->~{assumption})"), {step1})
    ante = prover.add_tautology(Formula.parse(f"~{contradiction}"))
    prover.add_mp(Formula.parse(f"~{assumption}"), ante, conse)
    return prover.qed()