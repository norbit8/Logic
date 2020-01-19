from predicates.completeness import *
SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES = frozenset({
    Formula.parse(s) for s in {
        'Plus(0,0,0)', '~Plus(1,0,0)', '~Plus(2,0,0)',
        '~Plus(3,0,0)', '~Plus(4,0,0)', '~Plus(5,0,0)',
        '~Plus(0,0,1)', 'Plus(1,0,1)', '~Plus(2,0,1)',
        '~Plus(3,0,1)', '~Plus(4,0,1)', '~Plus(5,0,1)',
        '~Plus(0,0,2)', '~Plus(1,0,2)', 'Plus(2,0,2)',
        '~Plus(3,0,2)', '~Plus(4,0,2)', '~Plus(5,0,2)',
        '~Plus(0,0,3)', '~Plus(1,0,3)', '~Plus(2,0,3)',
        'Plus(3,0,3)', '~Plus(4,0,3)', '~Plus(5,0,3)',
        '~Plus(0,0,4)', '~Plus(1,0,4)', '~Plus(2,0,4)',
        '~Plus(3,0,4)', 'Plus(4,0,4)', '~Plus(5,0,4)',
        '~Plus(0,0,5)', '~Plus(1,0,5)', '~Plus(2,0,5)',
        '~Plus(3,0,5)', '~Plus(4,0,5)', 'Plus(5,0,5)',
        '~Plus(0,1,0)', 'Plus(1,1,0)', '~Plus(2,1,0)',
        '~Plus(3,1,0)', '~Plus(4,1,0)', '~Plus(5,1,0)',
        '~Plus(0,1,1)', '~Plus(1,1,1)', 'Plus(2,1,1)',
        '~Plus(3,1,1)', '~Plus(4,1,1)', '~Plus(5,1,1)',
        '~Plus(0,1,2)', '~Plus(1,1,2)', '~Plus(2,1,2)',
        'Plus(3,1,2)', '~Plus(4,1,2)', '~Plus(5,1,2)',
        '~Plus(0,1,3)', '~Plus(1,1,3)', '~Plus(2,1,3)',
        '~Plus(3,1,3)', 'Plus(4,1,3)', '~Plus(5,1,3)',
        '~Plus(0,1,4)', '~Plus(1,1,4)', '~Plus(2,1,4)',
        '~Plus(3,1,4)', '~Plus(4,1,4)', 'Plus(5,1,4)',
        'Plus(0,1,5)', '~Plus(1,1,5)', '~Plus(2,1,5)',
        '~Plus(3,1,5)', '~Plus(4,1,5)', '~Plus(5,1,5)',
        '~Plus(0,2,0)', '~Plus(1,2,0)', 'Plus(2,2,0)',
        '~Plus(3,2,0)', '~Plus(4,2,0)', '~Plus(5,2,0)',
        '~Plus(0,2,1)', '~Plus(1,2,1)', '~Plus(2,2,1)',
        'Plus(3,2,1)', '~Plus(4,2,1)', '~Plus(5,2,1)',
        '~Plus(0,2,2)', '~Plus(1,2,2)', '~Plus(2,2,2)',
        '~Plus(3,2,2)', 'Plus(4,2,2)', '~Plus(5,2,2)',
        '~Plus(0,2,3)', '~Plus(1,2,3)', '~Plus(2,2,3)',
        '~Plus(3,2,3)', '~Plus(4,2,3)', 'Plus(5,2,3)',
        'Plus(0,2,4)', '~Plus(1,2,4)', '~Plus(2,2,4)',
        '~Plus(3,2,4)', '~Plus(4,2,4)', '~Plus(5,2,4)',
        '~Plus(0,2,5)', 'Plus(1,2,5)', '~Plus(2,2,5)',
        '~Plus(3,2,5)', '~Plus(4,2,5)', '~Plus(5,2,5)',
        '~Plus(0,3,0)', '~Plus(1,3,0)', '~Plus(2,3,0)',
        'Plus(3,3,0)', '~Plus(4,3,0)', '~Plus(5,3,0)',
        '~Plus(0,3,1)', '~Plus(1,3,1)', '~Plus(2,3,1)',
        '~Plus(3,3,1)', 'Plus(4,3,1)', '~Plus(5,3,1)',
        '~Plus(0,3,2)', '~Plus(1,3,2)', '~Plus(2,3,2)',
        '~Plus(3,3,2)', '~Plus(4,3,2)', 'Plus(5,3,2)',
        'Plus(0,3,3)', '~Plus(1,3,3)', '~Plus(2,3,3)',
        '~Plus(3,3,3)', '~Plus(4,3,3)', '~Plus(5,3,3)',
        '~Plus(0,3,4)', 'Plus(1,3,4)', '~Plus(2,3,4)',
        '~Plus(3,3,4)', '~Plus(4,3,4)', '~Plus(5,3,4)',
        '~Plus(0,3,5)', '~Plus(1,3,5)', 'Plus(2,3,5)',
        '~Plus(3,3,5)', '~Plus(4,3,5)', '~Plus(5,3,5)',
        '~Plus(0,4,0)', '~Plus(1,4,0)', '~Plus(2,4,0)',
        '~Plus(3,4,0)', 'Plus(4,4,0)', '~Plus(5,4,0)',
        '~Plus(0,4,1)', '~Plus(1,4,1)', '~Plus(2,4,1)',
        '~Plus(3,4,1)', '~Plus(4,4,1)', 'Plus(5,4,1)',
        'Plus(0,4,2)', '~Plus(1,4,2)', '~Plus(2,4,2)',
        '~Plus(3,4,2)', '~Plus(4,4,2)', '~Plus(5,4,2)',
        '~Plus(0,4,3)', 'Plus(1,4,3)', '~Plus(2,4,3)',
        '~Plus(3,4,3)', '~Plus(4,4,3)', '~Plus(5,4,3)',
        '~Plus(0,4,4)', '~Plus(1,4,4)', 'Plus(2,4,4)',
        '~Plus(3,4,4)', '~Plus(4,4,4)', '~Plus(5,4,4)',
        '~Plus(0,4,5)', '~Plus(1,4,5)', '~Plus(2,4,5)',
        'Plus(3,4,5)', '~Plus(4,4,5)', '~Plus(5,4,5)',
        '~Plus(0,5,0)', '~Plus(1,5,0)', '~Plus(2,5,0)',
        '~Plus(3,5,0)', '~Plus(4,5,0)', 'Plus(5,5,0)',
        'Plus(0,5,1)', '~Plus(1,5,1)', '~Plus(2,5,1)',
        '~Plus(3,5,1)', '~Plus(4,5,1)', '~Plus(5,5,1)',
        '~Plus(0,5,2)', 'Plus(1,5,2)', '~Plus(2,5,2)',
        '~Plus(3,5,2)', '~Plus(4,5,2)', '~Plus(5,5,2)',
        '~Plus(0,5,3)', '~Plus(1,5,3)', 'Plus(2,5,3)',
        '~Plus(3,5,3)', '~Plus(4,5,3)', '~Plus(5,5,3)',
        '~Plus(0,5,4)', '~Plus(1,5,4)', '~Plus(2,5,4)',
        'Plus(3,5,4)', '~Plus(4,5,4)', '~Plus(5,5,4)',
        '~Plus(0,5,5)', '~Plus(1,5,5)', '~Plus(2,5,5)',
        '~Plus(3,5,5)', 'Plus(4,5,5)', '~Plus(5,5,5)'}})
is_primitively_closed(SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES)