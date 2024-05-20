From CoMoAlg Require Export Setoids.
From Coq Require Export Bool Setoid Lia Morphisms.

Class Group :=
  {
    base_Setoid :: Setoid;
    op : carr -> carr -> carr;
    op_combat :: Proper (carreq ==> carreq ==> carreq) op;
    op_assoc :
      forall x y z,
        (op x (op y z)) =s= (op (op x y) z);
    neutr : carr;
    op_neutr_l : 
      forall x, 
        (op neutr x) =s= x;
    inv : carr -> carr;
    op_inv_l : 
      forall x, 
        (op (inv x) x) =s= neutr
  }.

Declare Scope group_scope.

Infix "*" := op : group_scope.

Open Scope group_scope.

Section Group_Properties.

  Context `{G : Group}.

  Lemma op_inv_r : 
    forall x,
      (x * (inv x)) =s= neutr.
  Proof.
    intros x.
    rewrite <- op_neutr_l.
    rewrite <- op_inv_l with (x := inv x) at 1.
    remember (inv x) as y.
    remember (inv y) as z.
    transitivity (op z (op (op y x) y)).
    repeat rewrite op_assoc.
    reflexivity.
    subst.
    rewrite op_inv_l.
    rewrite op_neutr_l.
    rewrite op_inv_l.
    reflexivity.
  Qed.

  Lemma op_neutr_r : 
    forall x,
    x * neutr =s= x.
  Proof.
    intros x.
    rewrite <- op_inv_l.
    rewrite op_assoc.
    rewrite op_inv_r.
    rewrite op_neutr_l.
    reflexivity.
  Qed.

  Lemma neutr_unique : 
    forall e,
      (forall x, e * x =s= x) ->
      e =s= neutr.
  Proof.
    intros e H1.
    rewrite <- op_neutr_r with (x := e).
    rewrite H1.
    reflexivity.
  Qed.

  Lemma inv_unique : 
    forall x i,
      (i * x) =s= neutr ->
      i =s= (inv x).
  Proof.
    intros x i H1.
    rewrite <- op_neutr_r with (x := i).
    rewrite <- op_inv_r with (x := x).
    rewrite op_assoc.
    rewrite H1.
    rewrite op_neutr_l.
    reflexivity.
  Qed.

  Lemma shorten_l : 
    forall x y z,
      x * z =s= y * z ->
      x =s= y.
  Proof.
    intros * H1.
    rewrite <- op_neutr_r with (x := x).
    rewrite <- op_inv_r with (x := z).
    rewrite op_assoc.
    rewrite H1.
    rewrite <- op_assoc.
    rewrite op_inv_r.
    rewrite op_neutr_r.
    reflexivity.
  Qed.

  Lemma shorten_r : 
    forall x y z,
      x * y =s= x * z ->
      y =s= z.
  Proof.
    intros * H1.
    rewrite <- op_neutr_l with (x := y).
    rewrite <- op_inv_l with (x := x).
    rewrite <- op_assoc.
    rewrite H1.
    rewrite op_assoc.
    rewrite op_inv_l.
    rewrite op_neutr_l.
    reflexivity.
  Qed.

  Lemma inv_neutr : 
    (inv neutr) =s= neutr.
  Proof.
    symmetry.
    apply inv_unique.
    rewrite op_neutr_l.
    reflexivity.
  Qed.

  Lemma inv_op : 
    forall x y,
      inv (x * y) =s= (inv y) * (inv x).
  Proof.
    intros x y.
    apply shorten_l with (z := op x y).
    rewrite op_inv_l.
    transitivity (op (inv y) y).
    rewrite op_inv_l; reflexivity.
    rewrite <- op_assoc.
    apply op_combat.
    reflexivity.
    rewrite op_assoc.
    rewrite op_inv_l.
    rewrite op_neutr_l.
    reflexivity.
  Qed.

End Group_Properties.
