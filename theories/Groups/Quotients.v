From CoMoAlg Require Export Groups.Morphisms.

#[refine] Instance equiv_Group {G H : Group} (phi : @Morph G H) : Group :=
  {|
    base_Setoid := {|
      carr := carr;
      carreq x y:=
        @morph _ _ phi x =s= @morph _ _ phi y
    |};
    op := op;
    neutr := neutr;
    inv := inv
  |}.
Proof.
  all: simpl in *.
  -
    split.
    +
      intros x.
      reflexivity.
    +
      intros x y H1.
      symmetry.
      assumption.
    +
      intros x y z H1 H2.
      transitivity (morph y).
      all: assumption.
  -
    intros x1 x2 H1 y1 y2 H2.
    (*
       H1 : phi x1 = phi x2
       H2 : phi y1 = phi y2
       zZ : phi (x1 + y1) = phi (x2 + y2)
     *)
    rewrite morph_op.
    rewrite H1, H2.
    rewrite <- morph_op.
    reflexivity.
  -
    intros x y z.
    rewrite op_assoc.
    reflexivity.
  -
    intros x.
    rewrite op_neutr_l.
    reflexivity.
  -
     intros x.
     rewrite op_inv_l.
     reflexivity.
Defined.

Print equiv_Group.

Definition equiv_Morph_surj {G H : Group} (f : Morph G H) : Morph G (equiv_Group f).
Proof.
  refine {|
    morph := fun x => _
  |}.
  -
    intros x y H1.
    simpl.
    apply morph_combat.
    eassumption.
  -
    intros x y.
    apply morph_combat.
    reflexivity.
Defined.

Definition equiv_Morph_inj {G H : Group} (f : Morph G H) : Morph (equiv_Group f) H.
Proof.
  refine {|
    morph := fun x => _
  |}.
  -
    intros x y H1.
    simpl in H1.
    eassumption.
  -
    intros.
    simpl in *.
    apply morph_op.
Defined.

Section Noether.

  Context {G : Group}.
  Context {H : Group}.
  Context (f : @Morph G H).

  Lemma Noether_commut :
    forall x,
      (morph x) =s=
      (@morph _ _ (comp (equiv_Morph_inj f) (equiv_Morph_surj f)) x).
  Proof.
    reflexivity.
  Qed.

  Theorem Noether_inj : 
    forall x y,
      (@morph _ _ (equiv_Morph_inj f) x) =s= (@morph _ _ (equiv_Morph_inj f) y) ->
      x =s= y.
  Proof.
    intros x y H1.
    simpl in *.
    assumption.
  Qed.

End Noether.
