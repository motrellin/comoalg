(*
    CoMoAlg - Setoids (Basics)
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

From Coq Require Export Setoid RelationClasses Morphisms.

Generalizable Variables X Y.

(** * Setoids

In this algebraic approach, we use _Setoids_ instead of normal sets as a base
for further algebraic structures. This has the advantage of adding an equality
relation [carreq] on top of the carrier [carr]. One effect of this will be, that 
the typical isomorphism between the image of some homomorphism [f] and the 
factor group of the kernel will become trivial.
 *)

Class Setoid :=
  {
    carr : Type;
    carreq : carr -> carr -> Prop;
    carreq_equiv :: Equivalence carreq
  }.

(* Some technical stuff about notations: *)
Declare Scope setoid_scope.
Infix "=s=" := carreq (at level 70) : setoid_scope.
Open Scope setoid_scope.

(** * Morphisms

Morphisms between Setoids are just normal functions [morph] between the 
carriers, that must be compatible with the equatily relations [carreq].
 *)

Class Setoid_Morph (X Y : Setoid) := 
  {
    morph : @carr X -> @carr Y; 
    morph_combat :: Proper (carreq ==> carreq) morph
  }.

Section predicates.

  Context `(f : @Setoid_Morph X Y).

  Definition injective : Type :=
    forall x y,
      morph x =s= morph y ->
      x =s= y.

  Definition surjective : Type :=
    forall y,
      {x : carr | morph x =s= y}.

  (** A morphism is called _bijective_ if it has some inverse morphism. *)

  Definition bijective : Type :=
    {g : Setoid_Morph Y X |
      (forall (y : @carr Y), morph (morph y) =s= y) /\
      (forall (x : @carr X), morph (morph x) =s= x)
    }.

  Lemma bijective_injective : 
    bijective ->
    injective.
  Proof.
    intros [g [H1 H2]] x y H3.
    rewrite <- H2.
    rewrite H3.
    rewrite H2.
    reflexivity.
  Qed.

  Lemma bijective_surjective :
    bijective ->
    surjective.
  Proof.
    intros [g [H1 H2]] y.
    exists (morph y).
    rewrite H1.
    reflexivity.
  Qed.

  Lemma injective_surjective_bijective : 
    injective ->
    surjective ->
    bijective.
  Proof.
    unfold injective, surjective, bijective.
    intros H1 H2.
    unshelve eexists.
    {
      unshelve econstructor.
      -
        intros y.
        destruct (H2 y).
        exact x.
      -
        simpl.
        intros y1 y2 H3.
        destruct (H2 y1) as [x1 H4], (H2 y2) as [x2 H5].
        apply H1.
        rewrite H4.
        rewrite H5.
        exact H3.
    }
    split.
    -
      intros y.
      simpl.
      destruct (H2 y) as [x H3].
      exact H3.
    -
      intros x.
      simpl.
      destruct (H2 (morph x)) as [x' H3].
      apply H1.
      exact H3.
  Qed.
      
End predicates.
