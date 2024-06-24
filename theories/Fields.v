(*
    CoMoAlg - Field Theory (Basics)
    Copyright (C) 2024  Max Ole Elliger

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

From CoMoAlg Require Export Rings.

Class Field :=
  {
    base_Integrity_Ring :: Integrity_Ring;
    invM : {x : carr | ~ (x =s= 0)} -> carr;
    mul_div_l : 
    forall (x : {x : carr | ~ (x =s= 0)}),
      (invM x) * (proj1_sig x) =s= 1
  }.

Coercion base_Integrity_Ring : Field >-> Integrity_Ring.

Section Field_Properties.

  Context `{Field}.

  Lemma unit_not_0 : 
    forall x,
      unit x ->
      ~ (x =s= 0).
  Proof.
    intros x [r [H1 H2]] H3.
    apply one_neq_0.
    symmetry.
    rewrite H3 in H1.
    rewrite mul_0_l in H1.
    assumption.
  Qed.

  Lemma not_0_unit : 
    forall x,
      ~ (x =s= 0) ->
      unit x.
  Proof.
    intros x H1.
    unshelve eexists.
    apply invM.
    exists x.
    exact H1.
    split.
    -
      rewrite mul_comm.
      rewrite mul_div_l.
      reflexivity.
    -
      rewrite mul_div_l.
      reflexivity.
  Qed.

  Lemma one_unique : 
    forall e,
      ~ (e =s= 0) ->
      (forall x, e * x =s= x) ->
      e =s= 1.
  Proof.
    intros e H1 H2.
    apply unit_one_unique.
    apply not_0_unit.
    exact H1.
    simpl in *.
    exact H2.
  Qed.

  Lemma invM_unique : 
    forall x i (H1 : ~ (x =s= 0)),
      i * x =s= 1 ->
      i =s= invM (exist _ x H1).
  Proof.
    intros x i H1 H2.
    assert (H3 : unit i).
    {
      apply not_0_unit.
      intros H3.
      rewrite H3 in H2.
      rewrite mul_0_l in H2.
      apply one_neq_0.
      symmetry.
      exact H2.
    }
    apply not_0_unit in H1 as H4.
    pose proof (@inv_unique unit_Group (existT unit x H4) (existT unit i H3)) as H5.
    simpl in H5.
    destruct H4 as [x' [H6 H7]].
    apply H5 in H2 as H8.
    rewrite H8 in *.
  Admitted.

End Field_Properties.

Class Ordered_Field :=
  {
    base_Field :: Field;
    positive : carr -> Prop;
    positive_compat :: Proper (carreq ==> iff) positive;
    positive_cases : (* TODO xor-functionality *)
      forall x,
        positive x \/
        positive (- x) \/
        x =s= 0;
    positive_add :
      forall x y,
        positive x ->
        positive y ->
        positive (x + y);
    positive_mul : 
      forall x y,
        positive x ->
        positive y ->
        positive (x * y);
  }.

Section comparing.

  Context `{Ordered_Field}.

  Definition gt x y := positive (x + - y).
  Definition ge x y := gt x y \/ x =s= y.
  Definition lt x y := gt y x.
  Definition le x y := ge y x.

  Infix ">" := gt : ring_scope.
  Infix ">=" := ge : ring_scope.
  Infix "<" := lt : ring_scope.
  Infix "<=" := le : ring_scope.

  Instance gt_compat : Proper (carreq ==> carreq ==> iff) gt.
  Proof.
    intros x1 x2 H1 y1 y2 H2.
    unfold ">".
    rewrite H1,H2.
    reflexivity.
  Qed.

  Lemma comparability : 
    forall x y,
      x < y \/
      x =s= y \/
      x > y.
  Proof.
    intros x y.
    destruct (positive_cases (x + - y)) as [H1|[H1|H1]].
    -
      right; right.
      assumption.
    -
      left.
      rewrite inv_op in H1.
      rewrite inv_inv in H1.
      assumption.
    -
      right; left.
      apply inv_unique in H1.
      rewrite inv_inv in H1.
      assumption.
  Qed.

  Lemma lt_transitive : Transitive lt.
  Proof.
    red.
    unfold lt,gt.
    intros x y z H1 H2.
    rewrite <- op_neutr_r with (x := z).
    rewrite <- op_inv_l with (x := y).
    rewrite op_assoc.
    rewrite <- op_assoc with (y := y).
    apply positive_add.
    all: assumption.
  Qed.

  Lemma lt_add : 
    forall x y z w,
      x < y ->
      z <= w ->
      x + z < y + w.
  Proof.
  Admitted.

  Lemma lt_mul : 
    forall x y z,
      x < y ->
      z > 0 ->
      x * z < y * z.
  Proof.
  Admitted.

  Lemma gt_neg : 
    forall x y,
      x < y ->
      - x > - y.
  Proof.
  Admitted.

  Lemma comparability_eq : 
    forall x y,
      x <= y \/
      x >= y.
  Proof.
  Admitted.

  Lemma le_ge_eq : 
    forall x y,
      x <= y ->
      x >= y ->
      x =s= y.
  Proof.
  Admitted.

  Lemma gt_mul : 
    forall x y z,
      x < y ->
      z < 0 ->
      x * z > y * z.
  Proof.
  Admitted.

  Lemma quadr_gt_0 : 
    forall x,
      ~ (x =s= 0) ->
      x * x > 0.
  Proof.
    intros x H1.
    red.
    rewrite inv_neutr.
    rewrite op_neutr_r.
    destruct (positive_cases x) as [H2|[H2|H2]].
    -
      apply positive_mul.
      all: assumption.
    -
      assert (H3 : x * x =s= - x * - x).
      {
        rewrite mul_inv_r.
        rewrite mul_inv_l.
        rewrite inv_inv.
        reflexivity.
      }
      rewrite H3.
      apply positive_mul.
      all: assumption.
    -
      contradiction.
  Qed.

  Remark one_gt_0 : 1 > 0.
  Proof.
    assert (H1 : 1 =s= (inv 1) * (inv 1)).
    rewrite mul_inv_l.
    rewrite mul_inv_r.
    rewrite inv_inv.
    rewrite mul_one_l.
    reflexivity.
    rewrite H1.
    apply quadr_gt_0.
    intros H2.
    apply one_neq_0.
    rewrite H1.
    rewrite H2.
    rewrite mul_0_l.
    reflexivity.
  Qed.

  Definition subset_add (A B : carr -> Prop) : carr -> Prop := 
    fun x =>
    exists y z,
      A y /\
      B z /\
      x =s= y + z.

  Lemma subset_add_comm : 
    forall A B x,
      subset_add A B x ->
      subset_add B A x.
  Proof.
    intros A B x [y [z [H1 [H2 H3]]]].
    exists z,y.
    repeat split.
    all: auto.
    rewrite op_comm.
    assumption.
  Qed.

  Lemma subset_add_assoc : 
    forall A B C x,
      subset_add A (subset_add B C) x <->
      subset_add (subset_add A B) C x.
  Proof.
  Admitted.

  Definition subset_mul (A B : carr -> Prop) : carr -> Prop := 
    fun x =>
    exists y z,
      A y /\
      B z /\
      x =s= y * z.

  Definition subset_le (x : carr) (A : carr -> Prop) : Prop := 
    forall y,
      A y ->
      x <= y.

  Definition subset_ge (x : carr) (A : carr -> Prop) : Prop := 
    forall y,
      A y ->
      x >= y.

  Definition subset_lt (x : carr) (A : carr -> Prop) : Prop :=
    forall y,
      A y ->
      x < y.

  Definition subset_gt (x : carr) (A : carr -> Prop) : Prop :=
    forall y,
      A y ->
      x > y.

  Definition max (A : carr -> Prop) (x : carr) : Prop := 
    subset_ge x A /\
    A x.

  Lemma max_unique : 
    forall A x y,
      max A x ->
      max A y ->
      x =s= y.
  Proof.
    intros A x y H1 H3.
    destruct H1 as [H1 H2].
    destruct H3 as [H3 H4].
    red in H1,H3.
    apply le_ge_eq.
    -
      red.
      apply H3.
      exact H2.
    -
      apply H1.
      exact H4.
  Qed.

  Definition min (A : carr -> Prop) (x : carr) : Prop :=
    subset_le x A /\
    A x.

  Lemma min_unique : 
    forall A x y,
      min A x ->
      min A y ->
      x =s= y.
  Proof.
    intros A x y H1 H3.
    destruct H1 as [H1 H2].
    destruct H3 as [H3 H4].
    red in H1,H3.
    apply le_ge_eq.
    -
      red.
      apply H1.
      exact H4.
    -
      apply H3.
      exact H2.
  Qed.

End comparing.
