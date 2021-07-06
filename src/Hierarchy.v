Require Import List Arith micromega.Lia.

From BY Require Import ListLemmas.

Class Monoid_op A := monoid_op : A -> A -> A.
Class Monoid_id A := monoid_id : A.
Class Monoid_inv A := monoid_inv : A -> A.

Typeclasses Transparent Monoid_op Monoid_id Monoid_inv.

Section __.
  Context
    {A : Type}
    {B : Type}
    {C : Type}
    {opA : A -> A -> A}
    {opB : B -> B -> B}
    {opC : C -> C -> C}
    {opABA : A -> B -> A}
    {opBAA : B -> A -> A}
    {opBAC : B -> A -> C}
    {opABC : A -> B -> C}
    {idA : A}
    {idA2 : A}
    {idB : B}
    {idC : C}
    {inv : A -> A}.

  Infix "∘" := opA (at level 50).
  Infix "+" := opB.
  Infix "*" := opC.
  Notation "x ⁻" := (inv x) (at level 1).

  Class Associative :=
    associative : forall x y z, x ∘ (y ∘ z) = (x ∘ y) ∘ z.
  Class Commutative :=
    commutative : forall x y, x ∘ y = y ∘ x.

  Class LeftIdentity :=
    left_identity : forall x, opBAA idB x = x.
  Class RightIdentity :=
    right_identity : forall x, opABA x idB = x.

  Class LeftInverse :=
    left_inverse : forall x, x⁻ ∘ x = idA.
  Class RightInverse :=
    right_inverse : forall x, x ∘ x⁻ = idA.

  Class LeftDistributive :=
    left_distributive : forall x y z, opBAC x (opA y z) = opC (opBAC x y) (opBAC x z).
  Class RightDistributive :=
    right_distributive : forall x y z, opABC (opA x y) z = opC (opABC x z) (opABC y z).

  Class LeftAction :=
    left_action : forall x y z, opBAA (opB x y) z = opBAA x (opBAA y z).
  Class RightAction :=
    right_action : forall x y z, opABA x (opB y z) = opABA (opABA x y) z.

  Class ZeroRule1 :=
    zero_rule1 : forall x y, opABC x y = idC -> x = idA \/ y = idB.
  Class ZeroRule2 :=
    zero_rule2 : forall x y, x <> idA -> y <> idB -> opABC x y <> idC.

  Class NonTrivial :=
    non_trivial : idA <> idA2.
End __.

Section __.
  Context
    {A}
    `{Monoid_op A}
    `{Monoid_id A}
    `{Monoid_inv A}.

  Class monoid :=
    {
      monoid_associative :> @Associative _ (monoid_op : A -> A -> A);
      monoid_left_identity :> @LeftIdentity _ _ monoid_op monoid_id;
      monoid_right_identity :> @RightIdentity _ _ monoid_op monoid_id
    }.

  Class commutative_monoid :=
    {
      commutative_monoid_monoid :> monoid;
      commutative_monoid_commutative :> @Commutative _ monoid_op
    }.

  Class group :=
    {
      group_monoid :> monoid;
      group_left_inverse :> @LeftInverse _ monoid_op monoid_id monoid_inv;
      group_right_inverse :> @RightInverse _ monoid_op monoid_id monoid_inv
    }.
End __.

Class Abelian_group_op A := abelian_group_op : A -> A -> A.
Class Abelian_group_id A := abelian_group_id : A.
Class Abelian_group_opp A := abelian_group_opp : A -> A.

Typeclasses Transparent Abelian_group_op Abelian_group_id Abelian_group_opp.

Instance abelian_group_op_monoid_op {A} `{op : Abelian_group_op A} : Monoid_op A := op.
Instance abelian_group_id_monoid_id {A} `{id : Abelian_group_id A} : Monoid_id A := id.
Instance abelian_group_opp_monoid_inv {A} `{opp : Abelian_group_opp A} : Monoid_inv A := opp.

Declare Scope group_scope.

Infix "+" := abelian_group_op : group_scope.
Notation "0" := abelian_group_id : group_scope.

Notation "- x" := (abelian_group_opp x) : group_scope.
Notation "x - y" := (abelian_group_op x (abelian_group_opp y)) : group_scope.

Section __.
  Context
    {A}
    `{Abelian_group_op A}
    `{Abelian_group_id A}
    `{Abelian_group_opp A}.

  Class abelian_group :=
    {
      abelian_group_group :> @group _ abelian_group_op_monoid_op abelian_group_id_monoid_id abelian_group_opp_monoid_inv;
      abelian_group_commutative_monoid :> @commutative_monoid _ abelian_group_op_monoid_op abelian_group_id_monoid_id
    }.
End __.

Class Ring_op A := ring_op : A -> A -> A.
Class Ring_id A := ring_id : A.

Instance ring_op_monoid_op {A} `{op : Ring_op A} : Monoid_op A := op.
Instance ring_id_monoid_id {A} `{id : Ring_id A} : Monoid_id A := id.

Typeclasses Transparent Ring_op Ring_id.

Declare Scope ring_scope.

Infix "*" := ring_op : ring_scope.
Notation "1" := ring_id : ring_scope.

Section __.
  Context
    {A}
    `{Abelian_group_op A}
    `{Ring_op A}
    `{Abelian_group_id A}
    `{Ring_id A}
    `{Abelian_group_opp A}.

  Open Scope group_scope.
  Open Scope ring_scope.

  Class ring :=
    {
      ring_group :> @abelian_group _ abelian_group_op abelian_group_id abelian_group_opp;
      ring_monoid :> @monoid _ ring_op_monoid_op ring_id_monoid_id;
      ring_left_distributive :> @LeftDistributive A A A abelian_group_op abelian_group_op ring_op;
      ring_right_distributive :> @RightDistributive A A A abelian_group_op abelian_group_op ring_op
    }.

  Class commutative_ring :=
    {
      commutative_ring_ring :> ring;
      commutative_ring_commutative_monoid :> @commutative_monoid _ ring_op_monoid_op ring_id_monoid_id
    }.

  Class non_trivial_ring :=
    {
      non_trivial_ring_ring :> ring;
      non_trivial_non_trivial :> @NonTrivial _ 0 1
    }.

  Class integral_domain :=
    {
      integral_domain_commutative_ring :> commutative_ring;
      integral_domain_non_trivial_ring :> non_trivial_ring;
      integral_domain_zero_rule :> @ZeroRule1 A A A ring_op 0 0 0
    }.
End __.

Class Module_left_act M R := module_left_act : R -> M -> M.
Class Module_right_act M R := module_right_act : M -> R -> M.

Typeclasses Transparent Module_left_act Module_right_act.

Declare Scope lmodule_scope.
Declare Scope rmodule_scope.

Infix "⋅" := module_left_act (at level 30) : lmodule_scope.
Infix "⋅" := module_right_act : rmodule_scope.

Section __.
  Context
    {M R}
    `{abelian_group M}
    `{ring R}
    `{Module_left_act M R}
    `{Module_right_act M R}.

  Class left_module :=
    {
      left_module_abelian_group :> @abelian_group M _ _ _;
      left_module_ring :> @ring R _ _ _ _ _;
      left_module_left_distributive :> @LeftDistributive M R M abelian_group_op abelian_group_op module_left_act;
      left_module_right_distributive :> @RightDistributive R M M abelian_group_op abelian_group_op module_left_act;
      left_module_left_act :> @LeftAction M R ring_op module_left_act;
      left_module_left_identity :> @LeftIdentity M R module_left_act ring_id
    }.
End __.

Section __.
  Context
    `{Associative}.

  Infix "∘" := opA (at level 50).

  Lemma fold_left_assoc (a b : A) ls :
    a ∘ (fold_left opA ls b) = fold_left opA ls (a ∘ b).
  Proof.
    revert b; induction ls; intros b; simpl.
    - reflexivity.
    - rewrite IHls, associative; reflexivity.
  Qed.
End __.

Declare Scope monoid_scope.

Infix "∘" := monoid_op (at level 50) : monoid_scope.
Notation "'id'" := monoid_id : monoid_scope.
Notation "x ⁻" := (monoid_inv x) (at level 1) : monoid_scope.

Section Monoid.
  Context
    `{monoid}.
  Open Scope monoid_scope.

  Global Instance mon_id_r : RightIdentity := right_identity.
  Global Instance mon_id_l : LeftIdentity := left_identity.

  Global Instance mon_assoc : Associative := associative.

  Context
    (f : nat -> A).

  Definition big_op_list (l : list nat) f := fold_left monoid_op (map f l) id.
  Definition big_op f n m := big_op_list (seq n (m - n)) f.
  Definition big_op_rev f n m := big_op_list (rev (seq n (m - n))) f.

  Hint Unfold big_op big_op_rev big_op_list : bigop.

  Lemma big_op_S_r n m (nltm : n <= m) :
    big_op f n (S m) = big_op f n m ∘ f m.
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, map_app, fold_left_app, <- le_plus_minus; auto. Qed.

  Lemma big_op_S_l n m (nltm : n <= m) :
    big_op f n (S m) = f n ∘ big_op f (S n) (S m).
  Proof. unfold big_op, big_op_list.
         rewrite Nat.sub_succ_l, fold_left_assoc; auto.
         simpl; rewrite (mon_id_l (f n)), (mon_id_r (f n)); auto. Qed.

  Lemma big_op_rev_S_r n m (nltm : n <= m) :
    big_op_rev f n (S m) = big_op_rev f (S n) (S m) ∘ f n.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l by auto; simpl; rewrite map_app, fold_left_app. reflexivity. Qed.

  Lemma big_op_rev_S_l n m (nltm : n <= m) :
    big_op_rev f n (S m) = f m ∘ big_op_rev f n m.
  Proof. unfold big_op_rev, big_op_list.
         rewrite Nat.sub_succ_l, seq_snoc, rev_app_distr, fold_left_assoc, <- le_plus_minus, (mon_id_r (f m)) by auto; simpl;
           rewrite (mon_id_l (f m)); auto. Qed.

  Lemma big_op_rev_nil n m (mltn : m <= n) :
    big_op_rev f n m = id.
  Proof. unfold big_op_rev; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_nil n m (mltn : m <= n) :
    big_op f n m = id.
  Proof. unfold big_op; replace (m - n) with 0 by lia; reflexivity. Qed.

  Lemma big_op_split n m k (nmk : n <= m <= k) :
    (big_op f n m) ∘ (big_op f m k) = big_op f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n = 0); assert (m = 0); subst; try lia. rewrite big_op_nil, mon_id_l. reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_nil (S k)), mon_id_r. reflexivity. lia.
      + rewrite big_op_S_r, mon_assoc, IHk, <- big_op_S_r by lia. reflexivity. Qed.

  Lemma big_op_rev_split n m k (nmk : n <= m <= k) :
    (big_op_rev f m k) ∘ (big_op_rev f n m) = big_op_rev f n k.
  Proof.
    revert nmk; revert n m. induction k; intros.
    - assert (n = 0); assert (m = 0); try lia; subst. rewrite big_op_rev_nil, mon_id_l. reflexivity. lia.
    - destruct (Nat.eq_dec m (S k)).
      + subst. rewrite (big_op_rev_nil (S k)), mon_id_l. reflexivity. lia.
      + rewrite big_op_rev_S_l, <- mon_assoc, IHk, <- big_op_rev_S_l by lia. reflexivity. Qed.

  Lemma big_op_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op f n m = big_op g (n + k) (m + k).
  Proof.
    intros. unfold big_op, big_op_list. apply f_equal2; [|reflexivity].
    replace (m + k - (n + k)) with (m - n) by lia.
    apply map_seq_ext; intros. rewrite H2. apply f_equal. lia. lia. Qed.

  Lemma big_op_rev_shift g n m k :
    (forall i, f i = g (i + k)) ->
    big_op_rev f n m = big_op_rev g (n + k) (m + k).
  Proof.
    intros. unfold big_op_rev, big_op_list. apply f_equal2; [|reflexivity].
    rewrite !map_rev. replace (m + k - (n + k)) with (m - n) by lia.
    apply f_equal; apply map_seq_ext; intros. rewrite H2; apply f_equal; lia. lia. Qed.
End Monoid.

Section Group.
  Context
    `{group}.

  Open Scope monoid_scope.

  Global Instance grp_inv_r : RightInverse := right_inverse.
  Global Instance grp_inv_l : LeftInverse := left_inverse.

  Global Instance grp_id_r : RightIdentity := right_identity.
  Global Instance grp_id_l : LeftIdentity := left_identity.

  Global Instance grp_assoc : Associative := associative.

  Lemma inv_unique_r : forall x y, x ∘ y = id -> y = x⁻.
  Proof.
    intros.
    apply (f_equal (monoid_op (monoid_inv x))) in H3.
    rewrite grp_assoc, grp_inv_l, grp_id_l, grp_id_r in H3.
    assumption.
  Qed.

  Lemma inv_unique_l : forall x y, y ∘ x = id -> y = x⁻.
  Proof.
    intros.
    apply (f_equal (fun a => a ∘ x⁻)) in H3.
    rewrite <- mon_assoc, grp_inv_r, mon_id_r, mon_id_l in H3.
    assumption.
  Qed.

  Lemma grp_r_inj : forall x y z, x ∘ y = x ∘ z -> y = z.
  Proof.
    intros.
    apply (f_equal (fun y => x⁻ ∘ y)) in H3.
    rewrite grp_assoc, grp_inv_l in H3.
    rewrite grp_assoc, grp_inv_l in H3.
    rewrite !grp_id_l in H3. assumption.
  Qed.

  Lemma grp_l_inj : forall y x z, x ∘ y = z ∘ y -> x = z.
  Proof.
    intros.
    apply (f_equal (fun x => x ∘ y⁻)) in H3.
    rewrite <- grp_assoc, grp_inv_r in H3.
    rewrite <- grp_assoc, grp_inv_r in H3.
    rewrite !grp_id_r in H3. assumption.
  Qed.

  Lemma inv_op : forall x y, (x ∘ y)⁻ = y⁻ ∘ x⁻.
  Proof.
    intros. symmetry.
    apply inv_unique_r.
    rewrite grp_assoc.
    rewrite <- (grp_assoc x y _).
    rewrite grp_inv_r.
    rewrite grp_id_r.
    rewrite grp_inv_r.
    reflexivity.
  Qed.

  Lemma id_inv : id⁻ = id.
  Proof.
    apply (grp_l_inj id).
    rewrite grp_inv_l.
    rewrite grp_id_r.
    reflexivity.
  Qed.

  Lemma inv_invol : forall x, x⁻⁻ = x.
  Proof.
    intros. symmetry; apply inv_unique_r. apply grp_inv_l.
  Qed.

  Lemma inv_inj : forall x y, x⁻ = y⁻ -> x = y.
  Proof.
    intros. rewrite <- (inv_invol x), <- (inv_invol y). rewrite H3. reflexivity.
  Qed.

  Lemma inv_id : forall x, x⁻ = id -> x = id.
  Proof.
    intros.
    rewrite <- (inv_invol x).
    rewrite H3.
    apply id_inv.
  Qed.
End Group.

Section AbelianGroup.

  Context
    `{abelian_group}.

  Open Scope group_scope.

  Definition opp_unique_r : forall x y, x + y = 0 -> y = -x := inv_unique_r.
  Definition opp_unique_l : forall x y, y + x = 0 -> y = -x := inv_unique_l.

  Definition opp_invol : forall x, - (- x) = x := inv_invol.

  Definition opp_0 : forall x, - x = 0 -> x = 0 := inv_id.
  Definition opp0 : - 0 = 0 := id_inv.

  Definition opp_inj : forall x y, - x = - y -> x = y := inv_inj.

  Global Instance add_0_r : @RightIdentity _ _ abelian_group_op 0 := right_identity.
  Global Instance add_0_l : @LeftIdentity _ _ abelian_group_op 0 := left_identity.

  Global Instance add_assoc : @Associative _ abelian_group_op := associative.
  Global Instance add_comm : @Commutative  _ abelian_group_op := commutative.

  Global Instance add_opp_r : @RightInverse _ abelian_group_op 0 abelian_group_opp := right_inverse.
  Global Instance add_opp_l : @LeftInverse _ abelian_group_op 0 abelian_group_opp := left_inverse.

  Lemma opp_add : forall x y, - (x + y) = - x - y.
  Proof.
    intros; rewrite inv_op, add_comm; reflexivity.
  Qed.

End AbelianGroup.

Section Ring.
  Context
    `{ring}.

  Open Scope ring_scope.
  Open Scope group_scope.

  Global Instance mul_1_r : @RightIdentity _ _ ring_op 1 := right_identity.
  Global Instance mul_1_l : @LeftIdentity _ _ ring_op 1 := left_identity.

  Global Instance mul_assoc : @Associative _ ring_op := associative.

  Global Instance mul_add_distr_l : LeftDistributive := left_distributive.
  Global Instance mul_add_distr_r : RightDistributive := right_distributive.

  Lemma mul_0_r : forall x : A, x * 0 = 0.
  Proof.
    intros.
    replace (x * 0) with (x * 0 + 0) by (apply add_0_r).
    replace 0 with (x * 0 - x * 0) at 2 3 by (apply add_opp_r).
    rewrite add_assoc.
    rewrite <- mul_add_distr_l.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma mul_0_l : forall x, 0 * x = 0.
  Proof.
    intros.
    replace (0 * x) with (0 * x + 0) by (apply add_0_r).
    replace 0 with (0 * x - 0 * x) at 2 3 by (apply add_opp_r).
    rewrite add_assoc.
    rewrite <- mul_add_distr_r.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma opp_mul_l : forall x y, - (x * y) = - x * y.
  Proof.
    intros. symmetry.
    apply opp_unique_l.
    rewrite <- mul_add_distr_r.
    rewrite add_opp_l.
    apply mul_0_l.
  Qed.

  Lemma opp_mul_r : forall x y, - (x * y) = x * - y.
  Proof.
    intros. symmetry.
    apply opp_unique_l.
    rewrite <- mul_add_distr_l.
    rewrite add_opp_l.
    apply mul_0_r.
  Qed.
End Ring.

Section CommutativeRing.
  Context
    `{commutative_ring}.

  Global Instance mul_comm : @Commutative _ ring_op := commutative.

  Open Scope ring_scope.
  Open Scope group_scope.

  Lemma ring_ring_theory : @ring_theory A 0 1 abelian_group_op ring_op  (fun x y => x + (- y)) abelian_group_opp eq.
  Proof.
    split; intros.
    - apply add_0_l.
    - apply add_comm.
    - apply add_assoc.
    - apply mul_1_l.
    - apply mul_comm.
    - apply mul_assoc.
    - apply mul_add_distr_r.
    - reflexivity.
    - apply add_opp_r.
  Qed.

  Add Ring commutative_ring_is_ring : ring_ring_theory.

  Example ex1 : forall x y, x + y = y + x.
  Proof. intros. ring. Qed.

  Example ex2 : forall x, 0 + x = x.
  Proof. intros. ring. Qed.

  Example ex3 : forall x, 1 * x = x.
  Proof. intros. ring. Qed.
End CommutativeRing.

Section __.
  Context
    {A : Type}.

  Class decidable P :=
    dec : {P} + {~ P}.
End __.
Notation decidable_rel r := (forall x y, decidable (r x y)).

Section IntegralDomain.
  Context
    `{integral_domain}.

  Add Ring integral_domain_ring : ring_ring_theory.

  Open Scope ring_scope.
  Open Scope group_scope.

  Lemma mul_r_inj : forall x y z, y <> 0 -> x * y = z * y -> x = z.
  Proof.
    intros.
    assert ((x - z) * y = 0).
    rewrite mul_add_distr_r, H6.
    ring.
    apply zero_rule1 in H7.
    destruct H7.
    - apply opp_unique_l in H7. rewrite H7. ring.
    - contradiction.
  Qed.

  Lemma mul_l_inj : forall x y z, x <> 0 -> x * y = x * z -> y = z.
  Proof.
    intros.
    eapply mul_r_inj.
    exact H5.
    rewrite mul_comm, H6.
    ring.
  Qed.

  Global Instance integral_domain_zero_rule2 : @ZeroRule2 A A A ring_op 0 0 0.
  Proof.
    intros ? ? ? ? contra; apply zero_rule1 in contra; destruct contra; contradiction.
  Qed.
End IntegralDomain.

Section ModuleTheory.
  Context
    `{left_module}.

  Open Scope group_scope.
  Open Scope ring_scope.
  Open Scope lmodule_scope.

  Global Instance act_1_l : @LeftIdentity M R module_left_act 1 := left_module_left_identity.

  Lemma act_0_r : forall x, x ⋅ 0 = 0.
  Proof.
    intros.
    replace (x ⋅ 0) with (x ⋅ 0 + 0) by (apply add_0_r).
    replace 0 with (x ⋅ 0 - x ⋅ 0) at 2 3 by (apply add_opp_r).
    rewrite add_assoc.
    rewrite <- left_distributive.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma act_0_l : forall x, 0 ⋅ x = 0.
    intros.
    replace (0 ⋅ x) with (0 ⋅ x + 0) by (apply add_0_r).
    replace 0 with (0 ⋅ x - 0 ⋅ x) by (apply add_opp_r).
    rewrite add_assoc.
    rewrite <- right_distributive.
    rewrite add_0_r.
    reflexivity.
  Qed.

  Lemma opp_act : forall x y, - x ⋅ y = (- x) ⋅ y.
    intros. symmetry. apply opp_unique_r.
    rewrite <- right_distributive.
    rewrite add_opp_r.
    apply act_0_l.
  Qed.
End ModuleTheory.
