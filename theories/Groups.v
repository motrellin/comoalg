From CoMoAlg Require Export Setoids.
From Coq Require Export Bool Setoid Lia Morphisms.

Class Group :=
  {
    base_Setoid :: Setoid;
    op : carr -> carr -> carr;
    op_combat :: Proper (carreq ==> carreq ==> carreq) op;
    op_assoc :
      forall x y z,
        carreq (op x (op y z)) (op (op x y) z);
    neutr : carr;
    op_neutr_l : 
      forall x, 
        carreq (op neutr x) x;
    inv : carr -> carr;
    op_inv_l : 
      forall x, 
        carreq (op (inv x) x) neutr
  }.

Section Group_Properties.

  Context `{G : Group}.

  Lemma op_inv_r : 
    forall x,
      carreq (op x (inv x)) neutr.
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
      carreq (op x neutr) x.
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
      (forall x, carreq (op e x) x) ->
      carreq e neutr.
  Proof.
    intros e H1.
    rewrite <- op_neutr_r with (x := e).
    rewrite H1.
    reflexivity.
  Qed.

  Lemma inv_unique : 
    forall x i,
      carreq (op i x) neutr ->
      carreq i (inv x).
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
      carreq (op x z) (op y z) ->
      carreq x y.
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
      carreq (op x y) (op x z) ->
      carreq y z.
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
    carreq (inv neutr) neutr.
  Proof.
    symmetry.
    apply inv_unique.
    rewrite op_neutr_l.
    reflexivity.
  Qed.

  Lemma inv_op : 
    forall x y,
      carreq (inv (op x y)) (op (inv y) (inv x)).
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
