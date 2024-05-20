From Coq Require Export RelationClasses.

Class Setoid :=
  {
    carr : Type;
    carreq : carr -> carr -> Prop;
    carreq_equiv :: Equivalence carreq
  }.

Declare Scope setoid_scope.

Infix "=s=" := carreq (at level 70) : setoid_scope.

Open Scope setoid_scope.
