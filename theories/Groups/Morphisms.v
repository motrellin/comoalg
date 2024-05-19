Require Export CoMoAlg.Groups.

Class Morph (domain codomain : Group) :=
  {
    morph : @carr (@base_Setoid domain) -> @carr (@base_Setoid codomain);
    morph_combat :: Proper (carreq ==> carreq) morph;
    morph_op :
      forall x y,
        carreq (morph (@op domain x y)) (@op codomain (morph x) (morph y))
  }.

Module Group_Morph_trivial.

  Instance trivial_Morph (G H : Group) : Morph G H.
  Proof.
    refine {|
      morph := fun x => neutr
    |}.
    -
      intros x y H1.
      reflexivity.
    -
      intros.
      rewrite (op_neutr_l).
      reflexivity.
  Defined.

End Group_Morph_trivial.

Instance comp {F G H : Group} (g : Morph G H) (f : Morph F G) : Morph F H.
Proof with auto.
  refine {|
    morph := fun f => morph (morph f)
  |}.
  -
    intros x y H1.
    rewrite H1.
    f_equiv.
  -
    intros.
    (*
       (g (f (x + y))) 
       = g (f (x) + f (y))
       = g (f (x)) + g(f (y))
     *)
    etransitivity.

    apply morph_combat.
    apply morph_op.

    apply morph_op.
Defined.
