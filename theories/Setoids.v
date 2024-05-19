Require Export RelationClasses.

Class Setoid :=
  {
    carr : Type;
    carreq : carr -> carr -> Prop;
    carreq_equiv :: Equivalence carreq
  }.
