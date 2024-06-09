From CoMoAlg Require Export Rings.

Class Field :=
  {
    base_Integrity_Ring :: Integrity_Ring;
    invM : {x : carr | ~ (x =s= neutr)} -> carr;
    mul_div_l : 
    forall (x : {x : carr | ~ (x =s= neutr)}),
      (invM x) * (proj1_sig x) =s= one
  }.

Section quot_field.

  Context `(Integrity_Ring).

  Let Q := (carr * {x : carr | ~ x =s= 0})%type.

  Inductive quoteq : relation Q :=
    | quoteq_1 :
        forall a b c d,
          a * (proj1_sig d) =s= (proj1_sig b) * c ->
          quoteq (a,b) (c,d).

  Instance quoteq_equiv : Equivalence quoteq.
  Proof.
    split.
    -
      intros [a [b H1]].
      constructor.
      apply mul_comm.
    -
      intros [a [b H1]] [c [d H2]] H3.
      constructor.
      inversion H3; subst.
      simpl in *.
      symmetry.
      rewrite mul_comm with (x := d) (y := a).
      rewrite mul_comm with (x := c) (y := b).
      exact H4.
    -
      intros [a [b H1]] [c [d H2]] [e [f H3]] H4 H5.
      constructor.
      inversion H4; subst.
      inversion H5; subst.
      simpl in *.
      unshelve eapply shorten_l.
      apply inv; apply mul; [exact b | exact e].
      rewrite op_inv_r.
      assert (H8 : d * (a * f + - b * e) =s= 0).
      {
        rewrite mul_op_distr_1.
        rewrite mul_assoc with (x := d) (y := a) (z := f).
        rewrite mul_comm with (x := d) (y := a).
        rewrite H6.
        rewrite <- mul_assoc with (x := b) (y := c) (z := f).
        rewrite H7.
        rewrite mul_assoc with (x := b) (y := d) (z := e).
        rewrite mul_comm with (x := b) (y := d).
        rewrite mul_assoc with (x := d) (y := - b) (z := e).
        rewrite <- mul_op_distr_2.
        rewrite <- mul_op_distr_1.
        rewrite op_inv_r.
        rewrite mul_0_r.
        rewrite mul_0_l.
        reflexivity.
      }
      apply mul_0 in H8 as [H8|H8].
      +
        contradiction.
      +
        simpl in *.
        rewrite mul_inv_l in H8.
        exact H8.
  Qed.

  Definition Quot_Setoid : Setoid :=
    {|
      carr := Q;
      carreq := quoteq;
      carreq_equiv := quoteq_equiv
    |}.

  Definition addQ (x y : Q) : Q.
  Proof.
    destruct x as [a [b H1]].
    destruct y as [c [d H2]].
    split.
    -
      apply op; apply mul.
        exact a.
        exact d.
        exact b.
        exact c.
    -
      exists (b * d).
      auto using mul_neq_0.
  Defined.

  Instance addQ_compat : Proper (quoteq ==> quoteq ==> quoteq) addQ.
  Proof.
    intros [a [b H1]] [c [d H2]] H3 [e [f H4]] [g [h H5]] H6.
    simpl in *.
    constructor.
    inversion H3; subst.
    inversion H6; subst.
    simpl in *.
    rewrite mul_op_distr_2.
    rewrite mul_op_distr_1.
    f_equiv.
    +
      rewrite mul_comm with (x := a) (y := f).
      rewrite mul_assoc with (x := f * a) (y := d) (z := h).
      rewrite <- mul_assoc with (x := f) (y := a) (z := d).
      rewrite H7.
      rewrite mul_assoc with (x := f) (y := b) (z := c).
      rewrite mul_comm with (x := f) (y := b).
      rewrite mul_assoc with (x := b * f) (y := c) (z := h).
      reflexivity.
    +
      rewrite mul_comm with (x := d) (y := h).
      rewrite mul_assoc with (x := b * e) (y := h) (z := d).
      rewrite <- mul_assoc with (x := b) (y := e) (z := h).
      rewrite H8.
      rewrite mul_assoc with (x := b) (y := f) (z := g).
      rewrite mul_comm with (x := d) (y := g).
      rewrite mul_assoc.
      reflexivity.
  Qed.

  Lemma addQ_assoc : 
    forall x y z,
    quoteq
    (addQ x (addQ y z))
    (addQ (addQ x y) z).
  Proof.
    intros [a [b H1]] [c [d H2]] [e [f H3]].
    constructor.
    simpl in *.
    repeat rewrite mul_op_distr_1.
    repeat rewrite mul_op_distr_2.
    repeat rewrite mul_op_distr_1.
    repeat rewrite mul_op_distr_2.
    rewrite op_assoc.
    f_equiv.
    +
      f_equiv.
      *
        do 2 rewrite mul_comm with (y := d * f).
        do 2 rewrite <- mul_assoc with (x := d * f).
        do 2 rewrite mul_assoc with (x := a).
        do 2 rewrite mul_assoc with (x := b).
        rewrite mul_comm with (x := a) (y := b).
        reflexivity.
      *
        rewrite <- mul_assoc with (x := b) (y := c * f).
        rewrite <- mul_assoc with (x := b) (y := d * f).
        rewrite mul_comm with (x := c) (y := f).
        rewrite mul_comm with (x := d) (y := f).
        do 2 rewrite <- mul_assoc with (x := f).
        f_equiv.
        f_equiv.
        do 2 rewrite mul_comm with (x := b).
        do 2 rewrite <- mul_assoc with (y := b).
        do 2 rewrite mul_assoc with (x := c).
        do 2 rewrite mul_assoc with (x := d).
        rewrite mul_comm with (x := c).
        rewrite mul_assoc.
        reflexivity.
    +
      repeat rewrite <- mul_assoc with (x := b).
      f_equiv.
      repeat rewrite <- mul_assoc with (x := d).
      f_equiv.
      repeat rewrite mul_assoc.
      do 2 rewrite <- mul_comm with (x := b).
      repeat rewrite <- mul_assoc.
      f_equiv.
      do 2 rewrite mul_assoc.
      do 2 rewrite mul_comm with (y := d).
      do 2 rewrite <- mul_assoc.
      f_equiv.
      rewrite mul_comm.
      reflexivity.
  Qed.

  Lemma addQ_comm : 
    forall x y,
      quoteq (addQ x y) (addQ y x).
  Proof.
    intros [a [b H1]] [c [d H2]].
    constructor.
    simpl.
    rewrite mul_comm.
    f_equiv.
    apply mul_comm.
    rewrite op_comm.
    f_equiv.
    apply mul_comm.
    apply mul_comm.
  Qed.

  Definition Q0 : Q.
  Proof.
    split.
    -
      exact 0.
    -
      exists one.
      exact one_neq_0.
  Defined.

  Definition invQ : Q -> Q.
  Proof.
    intros [a b].
    split.
    -
      apply inv.
      exact a.
    -
      exact b.
  Defined.

  Definition Quot_Group : Group.
  Proof.
    refine {|
      base_Setoid := Quot_Setoid;
      op := addQ;
      op_compat := addQ_compat;
      op_assoc := addQ_assoc;
      neutr := Q0;
      inv := invQ
    |}.
    -
      intros [a [b H1]].
      constructor.
      simpl.
      rewrite mul_0_l.
      rewrite op_neutr_l.
      do 2 rewrite <- mul_assoc.
      rewrite mul_comm with (x := a) (y := b).
      reflexivity.
    -
      intros [a [b H1]].
      constructor.
      simpl.
      rewrite mul_0_r.
      rewrite mul_inv_l.
      rewrite mul_comm with (x := b) (y := a).
      rewrite op_inv_l.
      rewrite mul_0_l.
      reflexivity.
  Defined.
      
  Definition Quot_Abelian_Group : Abelian_Group :=
    {|
      base_Group := Quot_Group;
      op_comm := addQ_comm
    |}.

  Definition mulQ (x y : Q) : Q.
  Proof.
    destruct x as [a [b H1]].
    destruct y as [c [d H2]].
    split.
    -
      apply mul.
        exact a.
        exact c.
    -
      exists (mul b d).
      auto using mul_neq_0.
  Defined.

  Instance mulQ_compat : Proper (quoteq ==> quoteq ==> quoteq) mulQ.
  Proof.
    intros [a [b H1]] [c [d H2]] H3 [e [f H4]] [g [h H5]] H6.
    constructor.
    inversion H3; subst.
    inversion H6; subst.
    simpl in *.
    rewrite mul_assoc with (x := a * e).
    rewrite <- mul_assoc with (x := a).
    rewrite mul_comm with (x := e) (y := d).
    rewrite mul_assoc with (x := a).
    rewrite H7.
    repeat rewrite <- mul_assoc.
    rewrite H8.
    f_equiv.
    repeat rewrite mul_assoc.
    rewrite mul_comm with (x := c) (y := f).
    reflexivity.
  Qed.

  Lemma mulQ_comm : 
    forall x y,
      quoteq (mulQ x y) (mulQ y x).
  Proof.
    intros [a [b H1]] [c [d H2]].
    constructor.
    simpl.
    rewrite mul_comm with (x := a * c).
    rewrite mul_comm with (x := a).
    rewrite mul_comm with (x := d).
    reflexivity.
  Qed.

  Lemma mulQ_addQ_distr_1 : 
    forall x y z,
      quoteq
      (mulQ x (addQ y z))
      (addQ (mulQ x y) (mulQ x z)).
  Proof.
    intros [a [b H1]] [c [d H2]] [e [f H3]].
    constructor.
    simpl.
    repeat rewrite mul_op_distr_1.
    repeat rewrite mul_op_distr_2.
    f_equiv.
    +
      repeat rewrite mul_assoc.
      f_equiv.
      f_equiv.
      do 2 rewrite <- mul_assoc with (x := a * c).
      rewrite mul_comm with (x := a * c).
      repeat rewrite mul_assoc.
      f_equiv.
      f_equiv.
      rewrite <- mul_assoc with (x := f).
      rewrite mul_comm with (x := f).
      reflexivity.
    +
      rewrite mul_comm with (x := a) (y := e).
      repeat rewrite <- mul_assoc.
      rewrite mul_comm with (x := a).
      repeat rewrite mul_assoc.
      f_equiv.
      do 2 rewrite mul_comm with (y := e).
      repeat rewrite <- mul_assoc.
      f_equiv.
      rewrite mul_comm with (x := d).
      repeat rewrite mul_assoc.
      f_equiv.
      repeat rewrite <- mul_assoc.
      f_equiv.
      rewrite mul_comm with (x := b) (y := f).
      rewrite mul_assoc.
      reflexivity.
  Qed.

  Lemma mulQ_addQ_distr_2 : 
    forall x y z,
      quoteq
      (mulQ (addQ x y) z)
      (addQ (mulQ x z) (mulQ y z)).
  Proof.
    intros x y z.
    do 3 rewrite mulQ_comm with (y := z).
    rewrite mulQ_addQ_distr_1.
    reflexivity.
  Qed.

  Definition Quot_Ring : Ring.
  Proof.
    refine {|
      base_Abelian := Quot_Abelian_Group;
      mul := mulQ;
      mul_compat := mulQ_compat;
      mul_op_distr_1 := mulQ_addQ_distr_1;
      mul_op_distr_2 := mulQ_addQ_distr_2
    |}.
    -
      intros [a [b H1]] [c [d H2]] [e [f H3]].
      constructor.
      simpl.
      rewrite mul_assoc with (x := b) (y := d) (z := f).
      rewrite mul_comm with (x := b * d * f).
      f_equiv.
      apply mul_assoc.
  Defined.

  Definition Quot_Commutative_Ring : Commutative_Ring Quot_Ring.
  Proof.
    constructor.
    exact mulQ_comm.
  Defined.

  Definition Q1 : Q.
  Proof.
    split.
    -
      exact one.
    -
      exists one.
      exact one_neq_0.
  Defined.

  Definition Quot_Unital_Ring : Unital_Ring Quot_Ring.
  Proof.
    unshelve econstructor.
    exact Q1.
    simpl.
    intros [a [b H1]].
    constructor.
    simpl.
    do 2 rewrite <- mul_assoc.
    rewrite mul_comm with (x := a) (y := b).
    reflexivity.
  Defined.

  Definition Quot_Integrity_Ring : Integrity_Ring.
  Proof.
    refine {|
      base_Ring := Quot_Ring;
      commutative := Quot_Commutative_Ring;
      unital := Quot_Unital_Ring;
    |}.
    -
      simpl.
      intros H1.
      inversion H1 as [a b c d H2 [eq1 eq2] [eq3 eq4]].
      subst.
      simpl in *.
      rewrite mul_0_r in H2.
      apply mul_0 in H2.
      destruct H2 as [H2|H2]; contradict H2; exact one_neq_0.
    -
      intros [a [b H1]] [[c [d H2]] [H3 H4]].
      constructor.
      inversion H4 as [a' b' c' d' H5 [eq1 eq2] [eq3 eq4]]; subst.
      simpl in *.
      rewrite mul_0_r in H5.
      repeat apply mul_0 in H5 as [H5|H5].
      +
        rewrite H5.
        rewrite mul_0_l,mul_0_r.
        reflexivity.
      +
        exfalso.
        apply H3.
        constructor.
        simpl.
        rewrite H5.
        rewrite mul_0_l,mul_0_r.
        reflexivity.
      +
        contradict H5.
        exact one_neq_0.
  Defined.

  Definition Quot_Field : Field.
  Proof.
    unshelve refine {|
      base_Integrity_Ring := Quot_Integrity_Ring
    |}.
    -
      intros [[a [b H1]] H2].
      split.
      +
        exact b.
      +
        exists a.
        intros H3.
        apply H2.
        constructor.
        simpl.
        rewrite H3.
        rewrite mul_0_l,mul_0_r.
        reflexivity.
    -
      intros [[a [b H1]] H2].
      constructor.
      simpl.
      rewrite mul_comm with (x := a) (y := b).
      reflexivity.
  Defined.

  Print Assumptions Quot_Field.

End quot_field.
