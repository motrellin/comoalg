(*
    CoMoAlg - Field Theory (Basics)
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

From CoMoAlg Require Export Rings.

Class Field :=
  {
    base_Integrity_Ring :: Integrity_Ring;
    invM : {x : carr | ~ (x =s= 0)} -> carr;
    mul_div_l : 
    forall (x : {x : carr | ~ (x =s= 0)}),
      (invM x) * (proj1_sig x) =s= 1
  }.

