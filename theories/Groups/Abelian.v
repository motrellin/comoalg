(*
    CoMoAlg - Group Theory: Abelian Groups
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

Class Abelian_Group :=
  {
    base_Group :: Group;
    op_comm : 
      forall x y,
        carreq (op x y) (op y x)
  }.

Declare Scope abelian_scope.

Infix "+" := op : abelian_scope.
Notation "- x" := (inv x) : abelian_scope.

Open Scope abelian_scope.

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
