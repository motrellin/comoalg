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

From Coq Require Export RelationClasses Morphisms.

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

(** A morphism is called _bijective_ if it has some inverse morphism. *)

Definition bijective {X Y} (f : Setoid_Morph X Y) :=
  {g : Setoid_Morph Y X |
    (forall (y : @carr Y), morph (morph y) =s= y) /\
    (forall (x : @carr X), morph (morph x) =s= x)
  }.
