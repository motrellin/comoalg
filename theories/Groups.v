(*
    CoMoAlg - Group Theory (Basics)
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

From CoMoAlg Require Export Setoids.
From Coq Require Export Bool Setoid Lia.

Generalizable Variables F G H.

(** * Groups

A [Group] is defined on top of some base [Setoid] (via [base_Setoid]). It
consists of some operation [op], which is (again) compatible with the equality
relations [carreq] of the carriers [carr], see [op_compat]. This operation
should be associatve, see [op_assoc].

A group also has some (left) neutral element [neutr] s.t. [op_neutr_l] holds.

For every element [g] of the group, there exists some (left) inverse [inv g] 
s.t. [op_inv_l] holds.
 *)

Class Group :=
  {
    base_Setoid :: Setoid;
    op : carr -> carr -> carr;
    op_compat :: Proper (carreq ==> carreq ==> carreq) op;
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

(* Some stuff on notations: *)
Coercion base_Setoid : Group >-> Setoid.
Declare Scope group_scope.
Infix "*" := op : group_scope.
Open Scope group_scope.

(** ** Properties of Groups *)

Section Group_Properties.

  Context `{Group}.

  (** There is no empty group. *)
  Lemma carr_inhabited : inhabited carr.
  Proof.
    constructor.
    exact neutr.
  Qed.

  (** There is no diference between left and right inverses. *)
  Lemma op_inv_r : 
    forall x,
      (x * (inv x)) =s= neutr.
  Proof.
    intros x.
    rewrite <- op_neutr_l.
    rewrite <- op_inv_l with (x := inv x) at 1.
    remember (inv x) as y.
    remember (inv y) as z.
    transitivity (z * (y * x * y)).
    repeat rewrite op_assoc.
    reflexivity.
    subst.
    rewrite op_inv_l.
    rewrite op_neutr_l.
    rewrite op_inv_l.
    reflexivity.
  Qed.

  (** There is no diference between a left and right neutral element. *)
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

  (** The neutral element is unique. *)
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

  (** For every element of a group, the inverse of it is unique. *)
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

  (** The inverse of the neutral element is itself. *)
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
    apply shorten_l with (z := x * y).
    rewrite op_inv_l.
    transitivity (op (inv y) y).
    rewrite op_inv_l; reflexivity.
    rewrite <- op_assoc.
    apply op_compat.
    reflexivity.
    rewrite op_assoc.
    rewrite op_inv_l.
    rewrite op_neutr_l.
    reflexivity.
  Qed.

End Group_Properties.

(** * Abelian Groups

An Abelian Group is a [Group] whose operation [op] is _commutative_. This is
declared by [op_comm].
 *)

Class Abelian_Group :=
  {
    base_Group :: Group;
    op_comm : 
      forall x y,
        x * y =s= y * x
  }.

(* Again some notation: *)
Coercion base_Group : Abelian_Group >-> Group.
Declare Scope abelian_scope.
Infix "+" := op : abelian_scope.
Notation "- x" := (inv x) : abelian_scope.

(** ** Examples of Abelian Groups *)
(** *** Integers *)

Module Integers.

  Open Scope nat_scope.

  Definition Z : Type := nat*nat.

  Inductive diffeq : relation Z :=
    | diffeq_1 : 
        forall a b c d,
          a + d = b + c ->
          diffeq (a,b) (c,d).

  Definition addZ (x y : Z) : Z :=
    let (a,b) := x in
    let (c,d) := y in
    (a+c,b+d).

  Definition Z0 : Z := (0,0).

  Definition invZ (x : Z) : Z :=
    let (a,b) := x in
    (b,a).

  Instance Z_Group : Abelian_Group.
  Proof.
    unshelve refine {|
      base_Group := {|
        base_Setoid := {|
          carr := Z;
          carreq := diffeq
        |};
        op := addZ;
        neutr := Z0;
        inv := invZ
      |}
    |}.
    all: simpl in *.
    all: unfold carr in *.
    all: try split.
    all: repeat inversion 1.
    all: repeat intro.
    all: repeat match goal with
    | [x : Z |- _] => destruct x
    end.
    all: repeat inversion 1.
    all: try constructor.
    all: try lia.
  Defined.

End Integers.

(** * Group Morphisms

Group Morphisms are Setoid Morphism that respect the equality relations
[carreq] which is declared via [morph_op].
 *)

Class Morph (domain codomain : Group) :=
  {
    base_Morph :: Setoid_Morph domain codomain;
    morph_op :
      forall x y,
        morph (x * y) =s= (morph x) * (morph y)
  }.

Coercion base_Morph : Morph >-> Setoid_Morph.

(** ** Examples *)
(** *** Trivial Morphisms *)

Module Group_Morph_trivial.

  Instance trivial_Morph (G H : Group) : Morph G H.
  Proof.
    repeat unshelve econstructor.
    -
      intro; exact neutr.
    -
      intros x y H1.
      reflexivity.
    -
      intros.
      rewrite (op_neutr_l).
      reflexivity.
  Defined.

End Group_Morph_trivial.

(** *** Composition of morphisms *)

Instance comp `(g : @Morph G H) `(f : @Morph F G) : Morph F H.
Proof.
  repeat unshelve econstructor.
  -
    intro x.
    apply morph.
    apply morph.
    exact x.
  -
    intros x y H1.
    rewrite H1.
    f_equiv.
  -
    intros.
    simpl.
    etransitivity.

    apply morph_compat.
    apply morph_op.

    apply morph_op.
Defined.

(** ** Properties of Group Morphisms *)

Section Morph_Properties.

  Context `{Morph}.

  Lemma morph_neutr :
    morph neutr =s= neutr.
  Proof.
    Check shorten_l.
    symmetry.
    apply shorten_l with (z := morph (neutr)).
    transitivity (morph neutr).
    apply op_neutr_l.
    transitivity (morph (neutr * neutr)).
    rewrite op_neutr_l; reflexivity.
    apply morph_op.
  Qed.

  Lemma morph_inv : 
    forall g,
      morph (inv g) =s= inv (morph g).
  Proof.
    intros g.
    apply shorten_l with (z := morph g).
    transitivity neutr.
    rewrite <- morph_op.
    rewrite op_inv_l.
    exact morph_neutr.
    symmetry.
    apply op_inv_l.
  Qed.

End Morph_Properties.

(** The automorphisms of a group form a group. *)
Instance Auto_Group `{G : Group} : Group.
Proof.
  unshelve refine {|
    base_Setoid := {|
      carr := {phi : Morph G G & bijective phi};
      carreq :=
        fun phi psi =>
        let f := @morph _ _ (projT1 phi) in
        let g := @morph _ _ (projT1 psi) in
        forall x,
          f x =s= g x
    |};
    op :=
      fun phi psi =>
      let f := projT1 phi in
      let g := projT1 psi in
      existT _ (comp f g) _
  |}.
  -
    split.
    +
      repeat intro;
      reflexivity.
    +
      repeat intro;
      symmetry;
      auto.
    +
      repeat intro;
      etransitivity;
      eauto.
  -
    destruct phi as [phi H1], psi as [psi H3].
    subst f g.
    destruct H1 as [phi' [H1 H2]], H3 as [psi' [H3 H4]].
    red.
    unshelve eexists {|
      morph := fun x => @morph _ _ psi' (@morph _ _ phi' x)
    |}.
    +
      intros x y H5.
      rewrite H5.
      reflexivity.
    +
      split.
      *
        intros x.
        simpl.
        rewrite H3.
        rewrite H1.
        reflexivity.
      *
        intros x.
        simpl.
        rewrite H2.
        rewrite H4.
        reflexivity.
  -
    simpl.
    unshelve eexists {|
      base_Morph := {|
        morph := fun x => x
      |}
    |}.
    +
      easy.
    +
      reflexivity.
    +
      unshelve eexists {|
        morph := fun x => x
      |}.
      *
        easy.
      *
        split; reflexivity.
  -
    simpl.
    intros [phi H1].
    destruct H1 as [phi' [H1 H2]].
    unshelve eexists {|
      base_Morph := phi'
    |}.
    +
      intros x y.
      symmetry.
      rewrite <- (H2 (morph x * morph y)).
      rewrite morph_op.
      rewrite H1.
      rewrite H1.
      reflexivity.
    +
      simpl.
      exists phi.
      split; assumption.
  -
    simpl.
    intros x1 y1 H1 x2 y2 H2 x. 
    simpl in *.
    rewrite H1,H2.
    reflexivity.
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
  -
    simpl.
    intros phi x.
    destruct phi as [phi [phi' [H1 H2]]].
    rewrite H2.
    reflexivity.
Defined.
