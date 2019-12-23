from predicates.syntax import *
from predicates.proofs import *
# from predicates.functions import *


s = Schema(Formula.parse('(Q(c1,c2)->(R(c1)->R(c2)))'),
{'c1', 'c2', 'R'})
print(s.instantiate({'c1': Term.parse('plus(x,1)'),
'R': Formula.parse('Q(_,y)')}) == Formula.parse("(Q(plus(x,1),c2)->(Q(plus(x,1),y)->Q(c2,y)))"))
# (Q(plus(x,1),c2)->(Q(plus(x,1),y)->Q(c2,y)))

print(s.instantiate({'c1': Term.parse('plus(x,1)'),
'c2': Term.parse('c1'),'R': Formula.parse('Q(_,y)')}) == Formula.parse("(Q(plus(x,1),c1)->(Q(plus(x,1),y)->Q(c1,y)))"))

# (Q(plus(x,1),c1)->(Q(plus(x,1),y)->Q(c1,y)))

s = Schema(Formula.parse('(P()->P())'), {'P'})
print(s.instantiate({'P': Formula.parse('plus(a,b)=c')}) == Formula.parse("(plus(a,b)=c->plus(a,b)=c)"))

# (plus(a,b)=c->plus(a,b)=c)

# For the following schema:

s = Schema(Formula.parse('(Q(d)->Ax[(R(x)->Q(f(c)))])'),
{'R', 'Q', 'x', 'c'})

# the following succeeds:

print(s.instantiate({'R': Formula.parse('_=0'),
'Q': Formula.parse('x=_'),'x': 'w'}) == Formula.parse("(x=d->Aw[(w=0->x=f(c))])"))

# (x=d->Aw[(w=0->x=f(c))])

# however, the following returns ``None`` because ``'d'`` is not a
# template of the schema:

print(s.instantiate({'R': Formula.parse('_=0'),
'Q': Formula.parse('x=_'),'x': 'w','d': Term('z')}) == None)

# and the following returns ``None`` because ``'z'`` that is free in
# the assignment to ``'Q'`` is to become bound by a quantification in
# the instantiated schema formula:

print(s.instantiate({'R': Formula.parse('_=0'),
'Q': Formula.parse('s(z)=_'),'x': 'z'}) == None)

# and the following returns ``None`` because ``'y'`` in the
# instantiated argument ``'f(plus(a,y))'`` of the second invocation of
# ``'Q'`` is to become bound by the quantification in the formula
# substituted for ``'Q'``:

print(s.instantiate({'R': Formula.parse('_=0'),
'Q': Formula.parse('Ay[s(y)=_]'),'c': Term.parse('plus(a,y)')}) == None)