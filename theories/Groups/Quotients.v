(*
    CoMoAlg - Group Theory: Factor groups
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

Generalizable Variables G H.

#[refine] Instance equiv_Group `(phi : Group_Morph) : Group :=
  {|
    base_Setoid := {|
      carr := carr;
      carreq x y:=
        @morph _ _ phi x =s= @morph _ _ phi y
    |};
    op := op;
    neutr := neutr;
    inv := inv
  |}.
Proof.
  all: simpl in *.
  -
    split.
    +
      intros x.
      reflexivity.
    +
      intros x y H1.
      symmetry.
      assumption.
    +
      intros x y z H1 H2.
      transitivity (morph y).
      all: assumption.
  -
    intros x1 x2 H1 y1 y2 H2.
    rewrite morph_op.
    rewrite H1, H2.
    rewrite <- morph_op.
    reflexivity.
  -
    intros x y z.
    rewrite op_assoc.
    reflexivity.
  -
    intros x.
    rewrite op_neutr_l.
    reflexivity.
  -
     intros x.
     rewrite op_inv_l.
     reflexivity.
Defined.

Definition equiv_Morph_surj `(f : @Group_Morph G H) : Group_Morph G (equiv_Group f).
Proof.
  unshelve refine {|
    base_Setoid_Morph := {|
      morph := fun x => _
    |}
  |}.
  -
    exact x.
  -
    intros x y H1.
    simpl.
    apply morph_compat.
    eassumption.
  -
    intros x y.
    reflexivity.
Defined.

Definition equiv_Morph_inj `(f : @Group_Morph G H) : Group_Morph (equiv_Group f) H.
Proof.
  unshelve refine {|
    base_Setoid_Morph := {|
      morph := fun x => _
    |}
  |}.
  -
    simpl in *.
    apply (@morph _ _ f).
    exact x.
  -
    intros x y H1.
    simpl in H1.
    eassumption.
  -
    intros.
    simpl in *.
    apply morph_op.
Defined.

Section Noether.

  Context `(f : Group_Morph).

  Lemma Noether_commut :
    forall x,
      (morph x) =s=
      (@morph _ _ (comp (equiv_Morph_inj f) (equiv_Morph_surj f)) x).
  Proof.
    reflexivity.
  Qed.

  Theorem Noether_inj : 
    forall x y,
      (@morph _ _ (equiv_Morph_inj f) x) =s= (@morph _ _ (equiv_Morph_inj f) y) ->
      x =s= y.
  Proof.
    intros x y H1.
    simpl in *.
    assumption.
  Qed.

End Noether.
