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

Class Setoid :=
  {
    carr : Type;
    carreq : carr -> carr -> Prop;
    carreq_equiv :: Equivalence carreq
  }.

Declare Scope setoid_scope.

Infix "=s=" := carreq (at level 70) : setoid_scope.

Open Scope setoid_scope.

Class Setoid_Morph (X Y : Setoid) := 
  {
    morph : @carr X -> @carr Y; 
    morph_combat :: Proper (carreq ==> carreq) morph
  }.

Definition bijective {X Y} (f : Setoid_Morph X Y) :=
  {g : Setoid_Morph Y X |
    (forall y, @morph _ _ f (@morph _ _ g y) =s= y) /\
    (forall x, @morph _ _ g (@morph _ _ f x) =s= x)
  }.
