(*
    CoMoAlg - Group Theory: Actions
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

Generalizable Variables G X Y.

Class Action (G : Group) (X : Setoid) :=
  {
    action : @carr G -> @carr X -> @carr X;
    action_combat :: Proper (carreq ==> carreq ==> carreq) action;
    action_neutr : 
      forall x,
        carreq (action neutr x) x;
    action_assoc : 
      forall g2 g1 x,
        carreq (action (op g2 g1) x) (action g2 (action g1 x))
  }.

#[refine] Instance trivial_Action {G : Group} {X : Setoid} : Action G X :=
  {|
    action := fun g x => x
  |}.
Proof.
  all: easy.
Defined.

Class Equivariance `(@Action G X) `(@Action G Y) :=
  {
    equivariance : @carr X -> @carr Y;
    equivariance_combat :: Proper (carreq ==> carreq) equivariance;
    equivariance_action : 
      forall g x,
        carreq (equivariance (action g x)) (action g (equivariance x))
  }.

Instance action_equiv `(Action) : Equivalence (fun x y => exists g, carreq y (action g x)).
Proof.
  split.
  -
    exists neutr.
    rewrite action_neutr.
    reflexivity.
  -
    intros x y [g H1].
    exists (inv g).
    rewrite H1.
    rewrite <- action_assoc.
    rewrite op_inv_l.
    rewrite action_neutr.
    reflexivity.
  -
    intros x y z [g H1] [h H2].
    exists (op h g).
    rewrite H2.
    rewrite H1.
    rewrite action_assoc.
    reflexivity.
Defined.

Definition orbit `(Action) (x : carr) : carr -> Prop :=
  fun y =>
  exists g,
    carreq y (action g x).

Example trivial_Action_orbit `{Group} `{Setoid} :
  forall x y,
    orbit trivial_Action x y ->
    carreq x y.
Proof.
  intros x y H1.
  red in H1.
  destruct H1 as [g H1].
  simpl in H1.
  symmetry.
  assumption.
Qed.
