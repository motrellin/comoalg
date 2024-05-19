From CoMoAlg Require Export Groups.

Section subgroup.

  Context (G : Group).
  Context (subgroup : carr -> Prop).
  
  Hypothesis op_preserve :
    forall x y,
      subgroup x ->
      subgroup y -> 
      subgroup (op x y).

  Hypothesis neutr_preserve :
    subgroup neutr.

  Hypothesis inv_preserve :
    forall x,
      subgroup x ->
      subgroup (inv x).

  Instance Subgroup : Group.
  Proof.
    unshelve refine {|
      base_Setoid := {|
        carr := {x : carr | subgroup x};
        carreq := 
          fun xp yp =>
          let (x,hxp) := xp in
          let (y,hyp) := yp in
          carreq x y
        |};
      op := 
        fun xp yp =>
        let (x,hxp) := xp in
        let (y,hyp) := yp in
        exist _ (op x y) (op_preserve x y hxp hyp);
      neutr := exist _ neutr neutr_preserve;
      inv :=
        fun xp =>
        let (x,hxp) := xp in
        exist _ (inv x) (inv_preserve x hxp)
    |}.
    -
      split.
      +
        intros [x H1].
        reflexivity.
      +
        intros [] [] ?.
        symmetry; assumption.
      +
        intros [] [] [] ? ?.
        etransitivity; eassumption.
    -
      intros [x1 H1] [x2 H2] H3 [y1 H4] [y2 H5] H6.
      apply op_combat.
      all: assumption.
    -
      intros [x H1] [y H2] [z H3].
      apply op_assoc.
    -
      intros [x H1].
      apply op_neutr_l.
    -
      intros [x H1].
      apply op_inv_l.
  Defined.

End subgroup.
