(*
    CoMoAlg - Group Theory: Subgroups
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

Section subgroup.

  Context `(Group).
  Context (subgroup : carr -> Prop).
  
  Hypothesis op_preserve :
    forall x y,
      subgroup x ->
      subgroup y -> 
      subgroup (x * y).

  Hypothesis neutr_preserve :
    subgroup neutr.

  Hypothesis inv_preserve :
    forall x,
      subgroup x ->
      subgroup (inv x).

  Instance Subgroup : Group.
  Proof.
    unshelve refine {|
      base_Setoid := {|
        carr := {x : carr | subgroup x};
        carreq := 
          fun xp yp =>
          let (x,hxp) := xp in
          let (y,hyp) := yp in
          x =s= y
        |};
      op := 
        fun xp yp =>
        let (x,hxp) := xp in
        let (y,hyp) := yp in
        exist _ (x * y) (op_preserve x y hxp hyp);
      neutr := exist _ neutr neutr_preserve;
      inv :=
        fun xp =>
        let (x,hxp) := xp in
        exist _ (inv x) (inv_preserve x hxp)
    |}.
    -
      split.
      +
        intros [x H1].
        reflexivity.
      +
        intros [] [] ?.
        symmetry; assumption.
      +
        intros [] [] [] ? ?.
        etransitivity; eassumption.
    -
      intros [x1 H1] [x2 H2] H3 [y1 H4] [y2 H5] H6.
      apply op_compat.
      all: assumption.
    -
      intros [x H1] [y H2] [z H3].
      apply op_assoc.
    -
      intros [x H1].
      apply op_neutr_l.
    -
      intros [x H1].
      apply op_inv_l.
  Defined.

End subgroup.
