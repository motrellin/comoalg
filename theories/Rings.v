(*
    CoMoAlg - Ring Theory (Basics)
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

From CoMoAlg Require Export Groups.
From Coq Require Export Classical PeanoNat Decidable.
Import PeanoNat.Nat.

Open Scope abelian_scope.

(** * Rings *)

Class Ring :=
  {
    base_Abelian :: Abelian_Group;
    mul : carr -> carr -> carr;
    mul_compat :: Proper (carreq ==> carreq ==> carreq) mul;
    mul_assoc :
      forall x y z,
        (mul x (mul y z)) =s= (mul (mul x y) z);
    mul_op_distr_1 :
      forall x y z,
        mul x (y + z) =s= (mul x y) + (mul x z);
    mul_op_distr_2 : 
      forall x y z,
        mul (x + y) z =s= (mul x z) + (mul y z)
  }.

Coercion base_Abelian : Ring >-> Abelian_Group.

Declare Scope ring_scope.

Infix "*" := mul : ring_scope.
Notation "0" := neutr : ring_scope.

Open Scope ring_scope.

(** ** Properties of Rings *)

Section Ring_Properties.

  Context `{Ring}.

  Lemma mul_0_l : 
    forall r,
      0 * r =s= 0.
  Proof.
    intro r.
    unshelve eapply shorten_r.
    apply mul; [exact 0 | exact r].
    transitivity ((0 + 0) * r).
    
    rewrite mul_op_distr_2; reflexivity.

    rewrite op_neutr_l.
    rewrite op_neutr_r.
    reflexivity.
  Qed.

  Lemma mul_0_r : 
    forall r,
      r * 0 =s= 0.
  Proof.
    intro r.
    unshelve eapply shorten_l.
    apply mul; [exact r | exact 0].
    transitivity (r * (0 + 0)).
    
    rewrite mul_op_distr_1; reflexivity.

    rewrite op_neutr_l.
    rewrite op_neutr_l.
    reflexivity.
  Qed.

  Lemma mul_inv_l : 
    forall x y,
      (- x) * y =s= - (x * y).
  Proof.
    intros x y.
    unshelve eapply shorten_r.
    apply mul; [exact x | exact y].
    rewrite op_inv_r.
    rewrite <- mul_op_distr_2.
    rewrite op_inv_r.
    rewrite mul_0_l.
    reflexivity.
  Qed.

  Lemma mul_inv_r : 
    forall x y,
      x * (- y) =s= - (x * y).
  Proof.
    intros x y.
    unshelve eapply shorten_l.
    apply mul; [exact x | exact y].
    rewrite op_inv_l.
    rewrite <- mul_op_distr_1.
    rewrite op_inv_l.
    rewrite mul_0_r.
    reflexivity.
  Qed.

End Ring_Properties.

(** * Unital Rings *)

Class Unital_Ring `(Ring) :=
  {
    one : carr;
    mul_one_l : 
      forall x,
        one * x =s= x;
  }.

Notation "1" := one : ring_scope.

Section units.

  Context `{Unital_Ring}.

  Definition unit (x : carr) :=
    {r : carr |
      x * r =s= 1 /\
      r * x =s= 1
    }.

  Example one_unit : unit 1.
  Proof.
    exists 1.
    split.
    all: rewrite mul_one_l.
    all: reflexivity.
  Qed.

  Definition unit_Setoid : Setoid.
  Proof.
    unshelve econstructor.
    -
      exact {x : carr & unit x}.
    -
      intros [x H1] [y H2].
      apply carreq.
      exact x.
      exact y.
    -
      split.
      all: repeat intros [].
      reflexivity.
      symmetry; assumption.
      etransitivity; eauto.
  Defined.

  Definition unit_Group : Group.
  Proof.
    unshelve refine {|
      base_Setoid := unit_Setoid
    |}.
    -
      intros [x H1] [y H2].
      exists (x * y).
      destruct H1 as [x' [H11 H12]], H2 as [y' [H21 H22]].
      exists (y' * x').
      split.
      +
        rewrite mul_assoc.
        rewrite <- mul_assoc with (x := x).
        rewrite H21.
        rewrite <- mul_assoc.
        rewrite mul_one_l.
        rewrite H11.
        reflexivity.
      +
        rewrite mul_assoc.
        rewrite <- mul_assoc with (x := y').
        rewrite H12.
        rewrite <- mul_assoc.
        rewrite mul_one_l.
        rewrite H22.
        reflexivity.
    -
      exists 1.
      exists 1.
      split.
      all: rewrite mul_one_l.
      all: reflexivity.
    -
      intros [x [x' [H1 H2]]].
      exists x'.
      exists x.
      split; assumption.
    -
      intros [x1 H1] [x2 H2] eqx [y1 H3] [y2 H4] eqy.
      simpl in *.
      f_equiv; assumption.
    -
      intros [x H1] [y H2] [z H3].
      simpl.
      apply mul_assoc.
    -
      intros [].
      apply mul_one_l.
    -
      intros [x [x' [H1 H2]]].
      simpl.
      assumption.
  Defined.

  Corollary unit_mul_one_r : 
    forall x,
      unit x ->
      x * 1 =s= x.
  Proof.
    intros x H1.
    exact (@op_neutr_r unit_Group (existT _ x H1)).
  Qed.

  Corollary unit_one_unique : 
    forall e,
      unit e ->
      (forall x, e * x =s= x) ->
      e =s= 1.
  Proof.
    intros e H1 H2.
    apply (@neutr_unique unit_Group (existT _ e H1)).
    intros [x H3].
    simpl.
    exact (H2 x).
  Qed.

  (*TODO: Add the rest. *)

End units.


(** * Commutative Rings *)

Class Commutative_Ring `(Ring) :=
  {
    mul_comm :
      forall x y,
        x * y =s= y * x
  }.

(** * Integrity Rings *)

Definition zero_divisor `{Ring} (x : carr) := 
  exists r, 
    ~ (r =s= 0) /\
    x * r =s= 0.

Class Integrity_Ring :=
  {
    base_Ring :: Ring;
    commutative :: Commutative_Ring base_Ring;
    unital :: Unital_Ring base_Ring;
    one_neq_0 : ~ 1 =s= 0;
    zero_divisor_free :
      forall x,
        zero_divisor x ->
        x =s= 0
  }.

Coercion base_Ring : Integrity_Ring >-> Ring.

(** ** Properties of Integrity Rings *)

Section Integrity_Ring_Properties.

  Context `{Integrity_Ring}.

  Lemma mul_0 : 
    forall x y,
      x * y =s= 0 ->
      x =s= 0 \/ y =s= 0.
  Proof.
    intros x y H1.
    Locate decidable.
    assert (H2 : forall x y, decidable (x =s= y)).
    admit. (* TODO *)
    destruct (H2 x 0) as [H3|H3], (H2 y 0) as [H4|H4].
    all: try tauto.
    left.
    apply zero_divisor_free.
    red.
    firstorder.
  Admitted.

  Lemma mul_neq_0 : 
    forall x y,
      ~ (x =s= 0) ->
      ~ (y =s= 0) ->
      ~ (x * y =s= 0).
  Proof.
    intros x y H1 H2 H3.
    firstorder using mul_0.
  Qed.
    
End Integrity_Ring_Properties.

(** ** Examples *)
(** *** Integers *)

Module Z.

  Import Groups.Integers.

  Definition mulZ (x y : Z) : Z :=
    let (a,b) := x in
    let (c,d) := y in
    (a*c+b*d,a*d+b*c).

  Instance Z_Ring : Ring.
  Proof.
    refine {|
      base_Abelian := Z_Group;
      mul := mulZ
    |}.
    -
      repeat red.
      intros * * H1 * H2.
      destruct H1,H2.
      constructor.
      lia.
    -
      intros; simpl; destruct x,y,z; constructor; lia.
    -
      intros; simpl; destruct x,y,z; constructor; lia.
    -
      intros; simpl; destruct x,y,z; constructor; lia.
  Defined.

  Instance Z_Integrity_Ring : Integrity_Ring.
  Proof.
    unshelve refine {|
      base_Ring := Z_Ring;
    |}.
    refine {|
      one := (1,0)
    |}.
    all: try (try constructor; (repeat intros []); simpl; constructor; lia).
    -
      inversion 1; subst; lia.
    -
      intros [a b] [[c d] [H1 H2]].
      simpl in *.
      inversion H2 as [a' b' c' d' H3 [eq1 eq2] [eq3 eq4]].
      subst.
      constructor.
      f_equal.
      do 2 rewrite PeanoNat.Nat.add_0_r in H3.
      assert (H4 : c <> d).
      {
        intros H4.
        apply diffeq_0 in H4.
        contradiction.
      }
      clear H1 H2.
      generalize dependent b.
      induction a as [|a' IH].
      all: intros b H5.
      +
        simpl in *.
        destruct b as [|b'].
        *
          reflexivity.
        *
          exfalso; apply H4.
          apply -> mul_cancel_l.
          symmetry.
          exact H5.
          easy.
      +
        destruct b as [|b'].
        *
          assert (H6 : c + a' * c = d + a' * d). lia. clear H5.
          exfalso; apply H4.
          assert (H7 : S a' * c = S a' * d). lia. clear H6.
          apply -> mul_cancel_l.
          exact H7.
          easy.
        *
          f_equal.
          apply IH.
          simpl in H5.
          lia.
  Defined.

End Z.
