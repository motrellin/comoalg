From CoMoAlg Require Export Abelian.

Class Ring :=
  {
    base_group :: Abelian_Group;
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

Module Z.

  Import Groups.Abelian.Integers.

  Definition mulZ (x y : Z) : Z :=
    let (a,b) := x in
    let (c,d) := y in
    (a*c+b*d,a*d+b*c).

  Instance Z_Ring : Ring.
  Proof.
    refine {|
      base_group := Z_Group;
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
