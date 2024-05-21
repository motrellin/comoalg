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

Class Ring :=
  {
    base_Abelian :: Abelian_Group;
    mul : carr -> carr -> carr;
    mul_combat :: Proper (carreq ==> carreq ==> carreq) mul;
    mul_assoc :
      forall x y z,
        carreq (mul x (mul y z)) (mul (mul x y) z);
    mul_op_distr_1 :
      forall x y z,
        carreq (mul x (op y z)) (op (mul x y) (mul x z));
    mul_op_distr_2 : 
      forall x y z,
        carreq (mul (op x y) z) (op (mul x z) (mul y z))
  }.

Declare Scope ring_scope.

Infix "*" := mul : ring_scope.

Open Scope ring_scope.

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

End Z.
