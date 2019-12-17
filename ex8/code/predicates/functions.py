# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *

def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1
    new_relations = dict(model.relation_meanings)
    for func_name, m   in model.function_meanings.items():
        relation_name = function_name_to_relation_name(func_name)
        fr_set = set()
        for k,v in m.items():
            fr_set.add((v, ) + k)
        new_relations[relation_name] = fr_set
    return Model(model.universe, model.constant_meanings, new_relations)

def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2
    new_function_meaning = dict()
    new_relation_meaning = dict()
    for name, m in model.relation_meanings.items():
        function_dict = dict()
        func_name  = relation_name_to_function_name(name)
        if func_name in original_functions:
            for s in m:
                # if the function returns different arguments for the same arguments or the arity is not matching
                if s[1:] in function_dict.keys() or len(m) != (len(model.universe) ** (len(s[1:]))):
                    return None
                function_dict[s[1:]] = s[0]
            new_function_meaning[func_name] = function_dict
        else:
            new_relation_meaning[name] = m
    return Model(model.universe, model.constant_meanings, new_relation_meaning, new_function_meaning)

def helper(i,term, z):
    temp_arg = list(term.arguments)
    temp_arg[i] = z
    return Term(term.root,temp_arg)

def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    # Task 8.3
    l = []
    temp = term
    for i,t in enumerate(term.arguments):
        if is_function(t.root):
            l += compile_term(t)
            temp = helper(i, term, l[-1].arguments[0])
            term = temp
    l.append(Formula("=", (Term(fresh_variable_name_generator.__next__()), temp)))
    return l

def replace_realtion(l:List[Formula])->Formula:
    if len(l) == 1:
        return Formula(function_name_to_relation_name(l[0].arguments[1].root),l[0].arguments[1].arguments)
    else:
        return Formula("A",l[0].arguments[0].root,Formula("->",
                    Formula(function_name_to_relation_name(l[0].arguments[1].root),(l[0].arguments[0],) + l[0].arguments[1].arguments)
                       , replace_realtion(l[1:])))

def replace_relation_helper(formula) -> Formula:
    return replace_realtion(compile_term(Term(relation_name_to_function_name(formula.root),formula.arguments)))

def replace_equality(l:List[Formula])->Formula:
    if len(l) == 1:
        return Formula("=",l[0].arguments[1].arguments)
    else:
        return Formula("A",l[0].arguments[0].root,Formula("->",
                    Formula(function_name_to_relation_name(l[0].arguments[1].root),(l[0].arguments[0],) + l[0].arguments[1].arguments)
                       , replace_equality(l[1:])))

def replace_equality_helper(formula) -> Formula:
    print("bblaa ", formula)
    return replace_equality(compile_term(Term("r",formula.arguments)))



def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4
    if is_unary(formula.root):
        return Formula(formula.root,replace_functions_with_relations_in_formula(formula.first))
    if is_binary(formula.root):
        return Formula(formula.root,replace_functions_with_relations_in_formula(formula.first),
                       replace_functions_with_relations_in_formula(formula.second))
    if is_quantifier(formula.root):
        return Formula(formula.root,formula.variable, replace_functions_with_relations_in_formula(formula.predicate))
    if is_equality(formula.root):
        return replace_equality_helper(formula)
    if is_relation(formula.root):
        return replace_relation_helper(formula)

def verify_func(func: Tuple[str, int])->Set[Formula]:
    """
    Given a function return a formulas with relations only
    that ensures that the function can be converted in two ways
    specifically it creates two new formulas
    :param func: tuple with function name and number of arguments as a tuple
    :return: set of two formulas which verifies the function
    """
    relation_name = function_name_to_relation_name(func[0])
    first, all_vars, s = "", "", set()
    for var in range(func[1]):
        new_var = fresh_variable_name_generator.__next__()
        first = first + "A" + new_var + "["
        all_vars += "," + new_var
    first = (first + "Ey[{0}(y{1})]" + ("]" * func[1])).format(relation_name, all_vars)
    s.add(Formula.parse(first))
    s.add(Formula.parse("Ax[Ay[Az[(({0}(y{1})&{0}(z{1}))->y=z)]]]".format(relation_name, all_vars)))
    return s

def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function,arity in formula.functions()}
                           for formula in formulas]).intersection(
                               set.union(*[{relation for relation,arity in
                                            formula.relations()} for
                                           formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    s = set()
    for formula in formulas:
        s.add(replace_functions_with_relations_in_formula(formula))
        for func in formula.functions():
            s = s.union(verify_func(func))
    return s

def replace_equality_with_relations_in_formula(formula: Formula) -> Formula:
    """

    :param formula:
    :return:
    """
    if formula.root == "=":
        return Formula("SAME", formula.arguments)
    elif is_unary(formula.root):
        return Formula(formula.root, replace_equality_with_relations_in_formula(formula.first))
    elif is_binary(formula.root):
        return Formula(formula.root, replace_equality_with_relations_in_formula(formula.first),
                       replace_equality_with_relations_in_formula(formula.second))
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_equality_with_relations_in_formula(formula.predicate))
    else:
        return formula

def get_relation_restriction(relations: Set[Tuple[str, int]]) -> Set[Formula]:
    s = set()
    for relation in relations:
        f = ""
        first_vars, second_vars = [], []
        for v in range(relation[1]):
            first_vars.append(fresh_variable_name_generator.__next__())
        for v in range(relation[1]):
            second_vars.append(fresh_variable_name_generator.__next__())
        for ve in first_vars:
            f += "A" + ve + "["
        for ve in second_vars:
            f += "A" + ve + "["
        f += "("
        all_sames = []
        for v in range(relation[1]):
            all_sames.append("SAME({0},{1})".format(first_vars[v], second_vars[v]))
        if len(all_sames) == 1:
            f += all_sames[0]
        else:
            f += "(" * (len(all_sames) - 1)
            for same in all_sames:
                f += same + "&"
            f = f[:-1] + (")" * (len(all_sames) - 1))
        f += "->"
        f += "({0}({1})->{0}({2}))".format(relation[0], ",".join(first_vars), ",".join(second_vars))
        f += ")"
        f += "]" * (len(first_vars) * 2)
        s.add(Formula.parse(f))
    return s

def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}
    # Task 8.6
    s = set()
    for formula in formulas:
        s.add(replace_equality_with_relations_in_formula(formula))
        all_relations = formula.relations()
        s = s.union(get_relation_restriction(all_relations)) # adding al the restrictions
    s.add(Formula.parse("SAME(x,x)")) # reflexivity
    s.add(Formula.parse("(SAME(x,y)->SAME(y,x))")) # symmetry 1
    s.add(Formula.parse("(SAME(y,x)->SAME(x,y))")) # symmetry 2
    s.add(Formula.parse("((SAME(x,y)&SAME(y,z))->SAME(x,z))")) # transitivity
    return s
        
def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7
    all_sames = set()
    for element in model.universe:
        all_sames.add((element, element))
    new_realation_meanings = dict(model.relation_meanings)
    for item in all_sames:
        new_realation_meanings["SAME"] = all_sames
    return Model(model.universe, model.constant_meanings, new_realation_meanings, model.function_meanings)

def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8
