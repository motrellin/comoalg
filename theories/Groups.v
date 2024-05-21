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
From Coq Require Export Bool Setoid Lia Morphisms.

Generalizable Variables F G H.

(** * Groups *)

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

  Context `{Group}.

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

(** * Abelian Groups *)

Class Abelian_Group :=
  {
    base_Group :: Group;
    op_comm : 
      forall x y,
        x * y =s= y * x
  }.

Declare Scope abelian_scope.

Infix "+" := op : abelian_scope.
Notation "- x" := (inv x) : abelian_scope.

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

(** * Group Morphisms *)

Class Morph (domain codomain : Group) :=
  {
    morph : @carr (@base_Setoid domain) -> @carr (@base_Setoid codomain);
    morph_combat :: Proper (carreq ==> carreq) morph;
    morph_op :
      forall x y,
        morph (x * y) =s= (morph x) * (morph y)
  }.

Module Group_Morph_trivial.

  Instance trivial_Morph (G H : Group) : Morph G H.
  Proof.
    refine {|
      morph := fun x => neutr
    |}.
    -
      intros x y H1.
      reflexivity.
    -
      intros.
      rewrite (op_neutr_l).
      reflexivity.
  Defined.

End Group_Morph_trivial.

Instance comp `(g : @Morph G H) `(f : @Morph F G) : Morph F H.
Proof with auto.
  refine {|
    morph := fun f => morph (morph f)
  |}.
  -
    intros x y H1.
    rewrite H1.
    f_equiv.
  -
    intros.
    (*
       (g (f (x + y))) 
       = g (f (x) + f (y))
       = g (f (x)) + g(f (y))
     *)
    etransitivity.

    apply morph_combat.
    apply morph_op.

    apply morph_op.
Defined.
