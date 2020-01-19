# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for first-order predicate logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1
    if is_equality(formula.root) or is_relation(formula.root):
        return True
    if is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    if is_unary(formula.root):
        return is_quantifier_free(formula.first)
    if is_quantifier(formula.root):
        return False

def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2
    if not is_quantifier(formula.root):
        return is_quantifier_free(formula)
    else:
        return is_in_prenex_normal_form(formula.predicate)

def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))

def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)

def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.5
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    if is_quantifier_free(formula):
        prover.add_tautology(Formula.parse(f"(({formula}->{formula})&({formula}->{formula}))"))
        return formula, prover.qed()
    if is_quantifier(formula.root):
        f, p = uniquely_rename_quantified_variables(formula.predicate)
        ante = prover.add_proof(p.conclusion, p)
        fresh_var = next(fresh_variable_name_generator)
        x = formula.variable
        old_R = p.conclusion.first.first
        old_Q = p.conclusion.first.second
        R = old_R.substitute({x: Term.parse("_")})
        Q = old_Q.substitute({x: Term.parse("_")})
        new_Q = Q.substitute({"_": Term.parse(fresh_var)})
        d = {"R": R, "Q": Q, "x": x, "y": fresh_var}
        line_number, instance = 0, None
        if formula.root == "A":
            instance = Formula.parse(f"((({old_R}->{old_Q})&({old_Q}->{old_R}))->((A{formula.variable}[{old_R}]->A{fresh_var}[{new_Q}])&(A{fresh_var}[{new_Q}]->A{formula.variable}[{old_R}])))")
            conse = prover.add_instantiated_assumption(instance, ADDITIONAL_QUANTIFICATION_AXIOMS[14], d)
        else: # its E
            instance = Formula.parse(f"((({old_R}->{old_Q})&({old_Q}->{old_R}))->((E{formula.variable}[{old_R}]->E{fresh_var}[{new_Q}])&(E{fresh_var}[{new_Q}]->E{formula.variable}[{old_R}])))")
            conse = prover.add_instantiated_assumption(instance, ADDITIONAL_QUANTIFICATION_AXIOMS[15], d)
        # ante = prover.add_tautology(instance.first)
        prover.add_mp(instance.second, ante, conse)
        return instance.second.first.second, prover.qed()
    if is_binary(formula.root):
        f1, p1 = uniquely_rename_quantified_variables(formula.first)
        f2, p2 = uniquely_rename_quantified_variables(formula.second)
        line1 = prover.add_proof(p1.conclusion, p1)
        line2 = prover.add_proof(p2.conclusion, p2)
        R = formula
        Q = Formula(formula.root, f1, f2)
        prover.add_tautological_implication(Formula.parse(f"(({R}->{Q})&({Q}->{R}))"),{line1,line2})
        return Q, prover.qed()
    if is_unary(formula.root):
        f, p = uniquely_rename_quantified_variables(formula.first)
        line1 = prover.add_proof(p.conclusion, p)
        R = formula
        Q = Formula(formula.root, f)
        prover.add_tautological_implication(Formula.parse(f"(({R}->{Q})&({Q}->{R}))"),{line1})
        return Q, prover.qed()

def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    if is_quantifier_free(formula.first.predicate):
        formula_new = formula.first
        if formula_new .root == 'A':
            x = formula_new.variable
            old_R = formula_new.predicate
            R = formula_new.predicate.substitute({x: Term.parse("_")})
            prover.add_instantiated_assumption(Formula.parse(f"((~A{x}[{old_R}]->E{x}[~{old_R}])&(E{x}[~{old_R}]->~A{x}[{old_R}]))"), ADDITIONAL_QUANTIFICATION_AXIOMS[0] , {"x": x, "R": R})
            f = Formula.parse(f"E{x}[~{old_R}]")
            return f, prover.qed()
        else: #"E"
            x = formula_new.variable
            old_R = formula_new.predicate
            R = formula_new.predicate.substitute({x: Term.parse("_")})
            prover.add_instantiated_assumption(Formula.parse(f"((~E{x}[{old_R}]->A{x}[~{old_R}])&(A{x}[~{old_R}]->~E{x}[{old_R}]))"), ADDITIONAL_QUANTIFICATION_AXIOMS[1] , {"x": x, "R": R})
            f = Formula.parse(f"A{x}[~{old_R}]")
            return f, prover.qed()
    else:
        our_formula = formula.first
        f, p = pull_out_quantifications_across_negation(Formula("~", our_formula.predicate))
        line1 = prover.add_proof(p.conclusion, p)
        our_var = our_formula.variable
        if our_formula.root == "A":
            R = p.conclusion.first.first
            new_R = R.substitute({our_var: Term.parse("_")})
            Q = p.conclusion.first.second
            new_Q = Q.substitute({our_var: Term.parse("_")})
            instante = Formula.parse(f"((({R}->{Q})&({Q}->{R}))->((E{our_var}[{R}]->E{our_var}[{Q}])&(E{our_var}[{Q}]->E{our_var}[{R}])))")
            line2 = prover.add_instantiated_assumption(instante, ADDITIONAL_QUANTIFICATION_AXIOMS[15], {'R':new_R, 'Q':new_Q, 'x':our_var, 'y':our_var})
            line3 = prover.add_mp(instante.second, line1, line2)
            x = our_var
            old_R = our_formula.predicate
            R = our_formula.predicate.substitute({x: Term.parse("_")})
            line4 = prover.add_instantiated_assumption(Formula.parse(f"((~A{x}[{old_R}]->E{x}[~{old_R}])&(E{x}[~{old_R}]->~A{x}[{old_R}]))"), ADDITIONAL_QUANTIFICATION_AXIOMS[0] , {"x": x, "R": R})
            prover.add_tautological_implication(equivalence_of(formula, instante.second.first.second), {line4, line3})
            return instante.second.first.second, prover.qed()
        else: # "E"
            R = p.conclusion.first.first
            new_R = R.substitute({our_var: Term.parse("_")})
            Q = p.conclusion.first.second
            new_Q = Q.substitute({our_var: Term.parse("_")})
            instante = Formula.parse(f"((({R}->{Q})&({Q}->{R}))->((A{our_var}[{R}]->A{our_var}[{Q}])&(A{our_var}[{Q}]->A{our_var}[{R}])))")
            line2 = prover.add_instantiated_assumption(instante, ADDITIONAL_QUANTIFICATION_AXIOMS[14], {'R':new_R, 'Q':new_Q, 'x':our_var, 'y':our_var})
            line3 = prover.add_mp(instante.second, line1, line2)
            x = our_var
            old_R = our_formula.predicate
            R = our_formula.predicate.substitute({x: Term.parse("_")})
            line4 = prover.add_instantiated_assumption(Formula.parse(f"((~E{x}[{old_R}]->A{x}[~{old_R}])&(A{x}[~{old_R}]->~E{x}[{old_R}]))"), ADDITIONAL_QUANTIFICATION_AXIOMS[1] , {"x": x, "R": R})
            prover.add_tautological_implication(equivalence_of(formula, instante.second.first.second), {line4, line3})
            return instante.second.first.second, prover.qed()


def pull_out_quantifications_from_left_across_binary_operator(formula:
                                                              Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    op_dict = {('&', 'A'): 2, ('&', 'E'): 3, ('|', 'A'): 6, ('|', 'E'): 7, ('->', 'A'): 10, ('->', 'E'): 11, 'E': 15, 'A': 14}
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    if is_quantifier_free(formula.first):
        f,p = pull_out_quantifications_from_right_across_binary_operator(formula)
        return f,p
    if is_quantifier_free(formula.first.predicate):
        formula_new = formula.first
        op = formula.root
        kamat = formula.first.root
        new_kamat = kamat
        if op == "->":
            if kamat == 'A':
                new_kamat = 'E'
            else:
                new_kamat='A'
        x = formula_new.variable
        old_R = formula_new.predicate
        R = formula_new.predicate.substitute({x: Term.parse("_")})
        Q = formula.second
        insta = Formula.parse(f"((({kamat}{x}[{old_R}]{op}{Q})->{new_kamat}{x}[({old_R}{op}{Q})])&({new_kamat}{x}[({old_R}{op}{Q})]->({kamat}{x}[{old_R}]{op}{Q})))")
        prover.add_instantiated_assumption(insta,
                                           ADDITIONAL_QUANTIFICATION_AXIOMS[op_dict[(op, kamat)]] ,
                                           {"x": x, "R": R, "Q": Q})
        f = Formula.parse(f"{new_kamat}{x}[({old_R}{op}{Q})]")
        return f, prover.qed()
    else:
        op = formula.root
        new_f = Formula(op, formula.first.predicate, formula.second)
        f, p = pull_out_quantifications_from_left_across_binary_operator(new_f)
        our_formula = formula.first
        line1 = prover.add_proof(p.conclusion, p)
        our_var = our_formula.variable

        kamat = our_formula.root
        new_kamat = kamat
        if op == "->":
            if kamat == 'A':
                new_kamat = 'E'
            else:
                new_kamat='A'
        R = p.conclusion.first.first
        new_R = R.substitute({our_var: Term.parse("_")})
        Q = p.conclusion.first.second
        new_Q = Q.substitute({our_var: Term.parse("_")})
        instante = Formula.parse(f"((({R}->{Q})&({Q}->{R}))->(({new_kamat}{our_var}[{R}]->{new_kamat}{our_var}[{Q}])&({new_kamat}{our_var}[{Q}]->{new_kamat}{our_var}[{R}])))")
        line2 = prover.add_instantiated_assumption(instante, ADDITIONAL_QUANTIFICATION_AXIOMS[op_dict[new_kamat]], {'R':new_R, 'Q':new_Q, 'x':our_var, 'y':our_var})
        line3 = prover.add_mp(instante.second, line1, line2)
        x = our_var
        old_R = formula.first.predicate
        Q = formula.second
        R = our_formula.predicate.substitute({x: Term.parse("_")})
        insta = Formula.parse(f"((({kamat}{x}[{old_R}]{op}{Q})->{new_kamat}{x}[({old_R}{op}{Q})])&({new_kamat}{x}[({old_R}{op}{Q})]->({kamat}{x}[{old_R}]{op}{Q})))")
        line4 = prover.add_instantiated_assumption(insta,
                                           ADDITIONAL_QUANTIFICATION_AXIOMS[op_dict[(op, kamat)]] ,
                                           {"x": x, "R": R, "Q": Q})
        prover.add_tautological_implication(equivalence_of(formula, instante.second.first.second), {line4, line3})
        return instante.second.first.second, prover.qed()


def pull_out_quantifications_from_right_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2
    op_dict = {('&', 'A'): 4, ('&', 'E'): 5, ('|', 'A'): 8, ('|', 'E'): 9, ('->', 'A'): 12, ('->', 'E'): 13, 'E': 15, 'A': 14}
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    if is_quantifier_free(formula.second.predicate):
        formula_new = formula.second
        op = formula.root
        kamat = formula.second.root
        new_kamat = kamat
        x = formula_new.variable
        old_R = formula_new.predicate
        R = formula_new.predicate.substitute({x: Term.parse("_")})
        Q = formula.first
        insta = Formula.parse(f"((({Q}{op}{kamat}{x}[{old_R}])->{new_kamat}{x}[({Q}{op}{old_R})])&({new_kamat}{x}[({Q}{op}{old_R})]->({Q}{op}{kamat}{x}[{old_R}])))")
        prover.add_instantiated_assumption(insta,
                                           ADDITIONAL_QUANTIFICATION_AXIOMS[op_dict[(op, kamat)]] ,
                                           {"x": x, "R": R, "Q": Q})
        f = Formula.parse(f"{new_kamat}{x}[({Q}{op}{old_R})]")
        return f, prover.qed()
    else:
        op = formula.root
        new_f = Formula(op, formula.first, formula.second.predicate)
        f, p = pull_out_quantifications_from_right_across_binary_operator(new_f)
        our_formula = formula.second
        line1 = prover.add_proof(p.conclusion, p)
        our_var = our_formula.variable
        kamat = our_formula.root
        new_kamat = kamat
        R = p.conclusion.first.first
        new_R = R.substitute({our_var: Term.parse("_")})
        Q = p.conclusion.first.second
        new_Q = Q.substitute({our_var: Term.parse("_")})
        instante = Formula.parse(f"((({R}->{Q})&({Q}->{R}))->(({new_kamat}{our_var}[{R}]->{new_kamat}{our_var}[{Q}])&({new_kamat}{our_var}[{Q}]->{new_kamat}{our_var}[{R}])))")
        line2 = prover.add_instantiated_assumption(instante, ADDITIONAL_QUANTIFICATION_AXIOMS[op_dict[new_kamat]], {'R':new_R, 'Q':new_Q, 'x':our_var, 'y':our_var})
        line3 = prover.add_mp(instante.second, line1, line2)
        x = our_var
        old_R = formula.second.predicate
        Q = formula.first
        R = our_formula.predicate.substitute({x: Term.parse("_")})
        insta = Formula.parse(f"((({Q}{op}{kamat}{x}[{old_R}])->{new_kamat}{x}[({Q}{op}{old_R})])&({new_kamat}{x}[({Q}{op}{old_R})]->({Q}{op}{kamat}{x}[{old_R}])))")
        line4 = prover.add_instantiated_assumption(insta,
                                           ADDITIONAL_QUANTIFICATION_AXIOMS[op_dict[(op, kamat)]] ,
                                           {"x": x, "R": R, "Q": Q})
        prover.add_tautological_implication(equivalence_of(formula, instante.second.first.second), {line4, line3})
        return instante.second.first.second, prover.qed()


def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    flag_gorer = False
    if formula.root == '->':
        flag_gorer = True
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    if is_quantifier_free(formula.first):
        f,p = pull_out_quantifications_from_left_across_binary_operator(formula)
        return f,p
    mapper = {'A': 14, 'E': 15}
    f, p = pull_out_quantifications_from_left_across_binary_operator(formula)
    pull_left = prover.add_proof(p.conclusion, p)
    ff = formula.first
    lst_of_vars_and_quant = []
    while not is_quantifier_free(ff.predicate):
        lst_of_vars_and_quant.append((ff.variable, ff.root))
        ff = ff.predicate
    lst_of_vars_and_quant.append((ff.variable, ff.root))
    neg_dict = {"E": "A", "A": "E"}
    lst_of_vars_and_quant = list(map(lambda xy: (xy[0],xy[1]) if not flag_gorer else (xy[0], neg_dict[xy[1]]), lst_of_vars_and_quant))
    ff = ff.predicate
    second_formula = Formula(formula.root, ff, formula.second)
    f2, p2 = pull_out_quantifications_from_right_across_binary_operator(second_formula)
    pull_right = prover.add_proof(p2.conclusion, p2)
    old_R = second_formula
    old_Q = f2
    insta = None
    for x, quant in lst_of_vars_and_quant[::-1]:
        R = old_R.substitute({x: Term.parse("_")})
        Q = old_Q.substitute({x: Term.parse("_")})
        quantified_R = Formula(quant, x ,old_R)
        quantified_Q = Formula(quant, x ,old_Q)
        inst_a = equivalence_of(quantified_R, quantified_Q)
        inst_b = equivalence_of(old_R, old_Q)
        inst = Formula("->", inst_b, inst_a)
        one_line = prover.add_instantiated_assumption(inst, ADDITIONAL_QUANTIFICATION_AXIOMS[mapper[quant]], {'x': x, 'y': x, 'R': R, 'Q': Q})
        pull_right = prover.add_mp(inst.second, pull_right, one_line)
        old_R = quantified_R
        old_Q = quantified_Q
    final = inst.second.second.first
    final_formula = equivalence_of(formula, final)
    prover.add_tautological_implication(final_formula, {pull_right, pull_left})
    return final, prover.qed()


def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    mapper = {'A': 14, 'E': 15}
    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    if is_unary(formula.root):
        f, p = to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        line1 = prover.add_proof(p.conclusion, p)
        nf = Formula("~", f)
        inst = equivalence_of(formula,nf)
        # print(prover.qed())
        # print(inst)

        new_formula = Formula("~", f)
        final, p = pull_out_quantifications_across_negation(new_formula)
        line3 = prover.add_proof(p.conclusion, p)
        # print(prover.qed())
        # print(inst, line1)
        line4 = prover.add_tautological_implication(equivalence_of(formula, nf), {line1})
        line5 = prover.add_tautological_implication(equivalence_of(formula,final), {line4,line3})
        return final, prover.qed()
    if is_binary(formula.root):
        f1, p1 = to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        f2, p2 = to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        line1 = prover.add_proof(p1.conclusion, p1)
        line2 = prover.add_proof(p2.conclusion, p2)
        merged_formula = Formula(formula.root, f1, f2)
        feqfnew = equivalence_of(formula, merged_formula)
        line3 = prover.add_tautological_implication(feqfnew, {line1, line2})
        f, p = pull_out_quantifications_across_binary_operator(merged_formula)
        line4 = prover.add_proof(p.conclusion, p)
        feqfFinal = equivalence_of(formula, f)
        prover.add_tautological_implication(feqfFinal, {line3, line4})
        return f, prover.qed()
    if is_quantifier(formula.root):
        f, p = to_prenex_normal_form_from_uniquely_named_variables(formula.predicate)
        line = prover.add_proof(p.conclusion, p)
        new_formula = Formula(formula.root, formula.variable, f)
        new_formula2 = Formula(formula.root, formula.variable, p.conclusion.first.first)
        insta = Formula("->", p.conclusion,equivalence_of(new_formula2, new_formula))
        line2=prover.add_instantiated_assumption(insta, ADDITIONAL_QUANTIFICATION_AXIOMS[mapper[formula.root]],
                                           {'Q': new_formula.predicate.substitute({formula.variable:Term.parse("_")}),
                                            'R': new_formula2.predicate.substitute({formula.variable:Term.parse("_")}),
                                            'x': formula.variable, 'y':formula.variable})
        prover.add_mp(insta.second,line, line2)
        return new_formula, prover.qed()

    #    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
    #     '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
    # {'x', 'y', 'R', 'Q'}),
    # Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
    # '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
    # {'x', 'y', 'R', 'Q'}))
    #
    #

def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.10
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)
    new_formula, proof = uniquely_rename_quantified_variables(formula)
    line1 = prover.add_proof(proof.conclusion, proof)
    final, proof2 = to_prenex_normal_form_from_uniquely_named_variables(new_formula)
    line2 = prover.add_proof(proof2.conclusion, proof2)
    prover.add_tautological_implication(equivalence_of(formula, final), {line1, line2})
    return final, prover.qed()