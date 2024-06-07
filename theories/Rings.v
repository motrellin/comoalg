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
From Coq Require Export Classical PeanoNat.
Import PeanoNat.Nat.

Open Scope abelian_scope.

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
Notation "0" := neutr (only parsing) : ring_scope.

Open Scope ring_scope.

Definition nullteiler `{Ring} (x : carr) := 
  exists r, 
    ~ (r =s= 0) /\
    x * r =s= 0.

Class Integrity_Ring :=
  {
    base_Ring :: Ring;
    mul_comm : 
      forall x y,
        x * y =s= y * x;
    one : carr;
    mul_one_l : 
      forall x,
        one * x =s= x;
    nullteilerfrei :
      forall x,
        nullteiler x ->
        x =s= 0
  }.

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
      one := (1,0)
    |}.
    all: try ((repeat intros []); simpl; constructor; lia).
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
    -
      simpl in *.
      destruct b as [|b'].
      +
        reflexivity.
      +
        exfalso; apply H4.
        apply -> mul_cancel_l.
        symmetry.
        exact H5.
        easy.
    -
      destruct b as [|b'].
      +
        assert (H6 : c + a' * c = d + a' * d). lia. clear H5.
        exfalso; apply H4.
        assert (H7 : S a' * c = S a' * d). lia. clear H6.
        apply -> mul_cancel_l.
        exact H7.
        easy.
      +
        f_equal.
        apply IH.
        simpl in H5.
        lia.
  Defined.

End Z.
