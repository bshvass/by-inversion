Require Import ZArith.
Require Import List Bool Znumtheory Decidable.
Require Import Rbase Reals QArith micromega.Lia micromega.Lqa micromega.Lra Qreals.

From BY Require Import AppendixE AppendixF Divstep Zpower_nat Zlemmas BigOp PadicVal Matrix.

Import Z.
Local Open Scope Z.

Arguments Z.mul : simpl never.
Arguments Z.sub : simpl never.
Arguments Z.add : simpl never.

Local Coercion of_nat : nat >-> Z.

Notation big_sum := (@big_op _ Z.add 0%Z).
Notation big_sum_nat := (@big_op _ Nat.add 0%nat).

Section __.

  Context {f g : Z}.

  Context {f_odd : odd f = true}
          {g_even : even g = true}
          {g_non0 : g <> 0}.

  Notation e := (ord2 g).

  Local Fixpoint z i :=
    match i with
    | 0%nat => (split2 g - f) / 2
    | S i => (z i + (z i mod 2) * split2 g) / 2
    end.

  Notation sum j := (1 + big_sum (fun i => 2 * 2 ^+ i * (z i mod 2)) 0%nat j).

  Lemma z_eq j :
    z j = (sum j * split2 g - f) / 2 ^+ (S j).
  Proof.
    induction j; intros.
    - rewrite big_op_nil by lia; simpl.
      apply f_equal2; ring.
    - simpl.
      rewrite big_op_S_r.
      rewrite IHj at 1.
      rewrite (mul_comm 2 (_ * _)). rewrite <- Zdiv_Zdiv.
      replace ((1 + (big_sum _ _ _ + 2 * 2 ^+ j * (z j mod 2))) * split2 g - f) with
          ((1 + big_sum (fun i => 2 * 2 ^+ i * (z i mod 2)) 0%nat j%nat) * split2 g - f + (z j mod 2) * split2 g * (2 * 2 ^+ j))
        by ring.
      rewrite Z.div_add.
      reflexivity.
      rewrite Zpower_nat_mul_l. apply Zpower_nat_nonzero. lia.
      rewrite Zpower_nat_mul_l. apply Zpower_nat_nonneg. lia.
      lia. lia. Qed.
 
  Lemma divstep_lemma1 i j (i_bound : (1 <= i)%nat) (sum_bound : (1 <= j + i < S e)%nat) :
    divstep_iter i f (g / 2 ^+ i) j = (j + i, f, g / 2 ^+ (j + i)).
  Proof.
    induction j; intros.
    - simpl. reflexivity.
    - simpl.
      rewrite IHj. unfold divstep.
      assert (0 <? j + i = true). apply Z.ltb_lt. lia.
      assert (odd (g / 2 ^+ (j + i)) = false). apply negb_true_iff. rewrite negb_odd.

      apply even_divide. transitivity (2 ^+ (ord2 g - (j + i))). apply Zpower_nat_base_divide. lia.
      apply divide_lemma. apply Zpower_nat_pos_nonneg. lia.
      transitivity (2 ^+ (ord2 g)). apply Zpower_nat_divide. lia. apply pval_spec. apply g_non0. lia.
      rewrite <- Zpower_nat_is_exp. replace ((j + i) + (ord2 g - (j + i)))%nat with (ord2 g) by lia.
      apply pval_spec. apply g_non0. lia.

      rewrite Zmod_even. rewrite <- negb_odd. 
      
      rewrite H, H0. simpl. apply f_equal2; [apply f_equal2|]. lia. lia.

      rewrite mul_0_l, add_0_r, Zdiv_Zdiv. apply f_equal. ring.
      apply Zpower_nat_nonneg. lia. lia.     lia. Qed.
  
  Lemma divstep_lemma2 i j (j_bound : (0 <= j + i < S e)%nat) :
    divstep_iter (1 - e + i) (split2 g) (z i) j = (j + 1 - e + i, split2 g, z (j + i)).
  Proof.
    induction j.
    - reflexivity.
    - simpl.
      rewrite IHj. unfold divstep.
      assert (0 <? j + 1 - e + i = false). apply Z.ltb_ge. lia.
      rewrite H. simpl. apply f_equal2; [apply f_equal2|]. lia. lia. reflexivity. lia. Qed.

  Lemma divstep_lemma3 :
    divstep e f (split2 g) = (1 - e, split2 g, z 0).
  Proof.
    unfold divstep.
    assert (0 <? e = true).
    rewrite <- Nat2Z.inj_0.
    apply Z.ltb_lt. apply inj_lt. apply ord2_even. apply g_even. rewrite H.
    rewrite odd_split2. reflexivity. apply g_non0. Qed.
  
  Lemma z_div j :
    2 ^+ (S j) * z j  = sum j * split2 g - f.
  Proof.
    induction j; intros.
    - rewrite big_op_nil by lia; simpl.
      rewrite mul_1_r. rewrite <- Z_div_exact_2. ring. lia.
      rewrite Zmod_even.
      rewrite even_sub. rewrite <- !negb_odd.
      rewrite odd_split2, f_odd.  reflexivity. apply g_non0.
    - simpl. replace (2 * (2 * 2 ^+ j) * ((z j + z j mod 2 * split2 g) / 2)) with
                 (((2 ^+ S j) * z j) + (2 * 2 ^+ j) * (z j mod 2 * split2 g)).

      rewrite IHj. 
      rewrite big_op_S_r. lia. lia.
      
      rewrite (mul_comm 2 (2 * _)).
      rewrite <- (mul_assoc _ 2).
      rewrite <- Z_div_exact_2. simpl. ring. lia.
      destruct (mod2_dec (z j)).
      + rewrite e. rewrite mul_0_l. rewrite add_0_r. assumption.
      + rewrite <- Zplus_mod_idemp_l. rewrite e. rewrite mul_1_l.
        apply mod_divide. lia. apply even_divide. rewrite even_add.
        rewrite <- (negb_odd (split2 _)). rewrite odd_split2. reflexivity. apply g_non0. Qed.

  Lemma sum_odd j :
    odd (sum j) = true.
  Proof.
    induction j.
    - reflexivity.
    - rewrite big_op_S_r, add_assoc, odd_add, IHj, !odd_mul. reflexivity. lia. Qed.

  Lemma sum_bound j :
    1 <= sum j < 2 ^+ (S j).
  Proof.
    induction j.
    - rewrite big_op_nil; simpl; lia.
    - rewrite big_op_S_r. pose proof mod_pos_bound (z j) 2 ltac:(lia).
      rewrite <- Zpower_nat_mul_l. rewrite add_assoc.
      assert (2 * 2 ^+ j = 2 ^+ (S j)) by reflexivity. nia. lia. Qed.

  Notation q' := (1 + big_sum (fun i => 2 * 2 ^+ i * (z i mod 2)) 0%nat e).
  
  Lemma q'_div :
    (2 ^+ (S e) | q' * split2 g - f).
  Proof. eexists. symmetry. rewrite mul_comm. apply z_div. Qed.

  Lemma q'_odd :
    odd q' = true.
  Proof. apply sum_odd. Qed.

  Lemma q'_bound :
    1 <= q' < 2 ^+ (S e).
  Proof. apply sum_bound. Qed.

  Lemma q'q : q' = q f g.
  Proof. apply q_unique. apply f_odd. apply g_non0.
         split; [|split]. apply q'_odd. apply q'_bound. apply q'_div. Qed.

  (* Lemma z_spec : exists q', odd q' = true /\ (1 <= q' < 2 ^+ (S e)) /\ 2 ^+ (S e) * z e = q' * split2 g - f. *)
  (* Proof. *)
  
  (*   induction e eqn:E. *)
  (*   - exists 1. repeat split. lia. rewrite Nat.mul_0_r. unfold z. rewrite Zpower_nat_1. *)
  (*     rewrite <- Z_div_exact_full_2. lia. lia. apply mod_divide. lia. *)
  (*     apply even_divide. rewrite even_sub. *)
  (*     rewrite <- !negb_odd. rewrite f_odd. rewrite odd_split2. reflexivity. apply g_non0. *)
  (*   -  *)

  Theorem G1 :
    divstep_iter 1%nat f (g / 2) (2 * e) = (1 , split2 g , (- (f mod2 g)) / 2 ^+ S e).
  Proof.
    unfold mod_2.
    assert (0 < e)%nat. apply ord2_even. apply g_even.
    replace (- (f - q f g * split2 g)) with (q f g * split2 g - f) by ring.

    replace 2 with (2 ^+ 1) at 1 by reflexivity.
    replace (2 * e)%nat with ((e - 1) + (S e))%nat by lia.
    rewrite divstep_iter_add.
    rewrite divstep_lemma1.
    replace ((e - 1)%nat + 1%nat) with (of_nat e) by lia.
    replace ((e - 1) + 1)%nat with e by lia.
    rewrite divstep_iter_S'.
    fold (split2 g).
    rewrite divstep_lemma3.
    replace (1 - e) with (1 - e + of_nat 0) by lia. 
    rewrite divstep_lemma2.
    apply f_equal2; [apply f_equal2|]. lia. reflexivity.
    rewrite Nat.add_0_r.
    rewrite z_eq. rewrite q'q. reflexivity. lia. lia. lia. Qed.

End __.

Context {R0 R1 : Z}.
Context {R0_odd : odd R0 = true}
        {R1_even : even R1 = true}
        {R1_non0 : R1 <> 0}.

Local Notation R_ i := (R_ R0 R1 i).
Local Notation e i := (ord2 (R_ i)).

Theorem G2 j (H : R_ j <> 0) :
  divstep_iter 1 R0 (R1 / 2) (2 * (big_sum_nat (fun i => e (S i)) 0 j))%nat =
  (1, split2 (R_ j), (R_ (S j)) / 2).
Proof.
  induction j.
  - simpl. rewrite split2_odd by apply R0_odd. reflexivity.
  - rewrite R_S_S. Compute (10 mod2 0).
    replace (R_ (S j) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite big_op_S_r.
    rewrite Nat.mul_add_distr_l.
    rewrite divstep_iter_add.
    rewrite IHj.
    rewrite Zdiv_Zdiv, Zpower_nat_mul_r. 
    eapply G1.

    apply Zpower_nat_nonneg. lia. lia. apply R_nonzero_S. apply odd_nonzero. apply R0_odd.
    assumption. lia. Unshelve. apply odd_split2.
    apply R_nonzero_S. apply odd_nonzero. apply R0_odd.
    assumption. apply R_even. apply odd_nonzero. apply R0_odd.
    apply R1_even. assumption. Qed.

(* Local Notation t := (Nat.max 67 (Z.to_nat (up (log_1024_633 (vec_norm (IZR R0, IZR R1))))))%nat. *)

Theorem G3 :
  (exists t G, divstep_iter 1 R0 (R1 / 2) (2 * (big_sum_nat (fun i => e (S i)) 0 t))%nat = (1, G, 0) /\ abs G = gcd R0 R1) /\
  forall d f n, divstep_iter 1 R0 (R1 / 2) n = (d, f, 0) -> abs f = gcd R0 R1.
Proof. apply and_lemma. 
  destruct (F26_cor2 R0_odd R1_even) as [t [Rt_non0 RSt_0]]. exists t, (split2 (R_ t)); split.
  rewrite G2. rewrite RSt_0. rewrite Z.div_0_l. reflexivity. lia. assumption. apply E3. apply R0_odd. apply R1_even.
  apply RSt_0. apply Rt_non0. 

  intros.
  destruct H as [t [G [H1 H2]]].
  set (w := big_sum_nat (fun i : nat => e (S i)) 0 t) in *.
  assert ((d + (2 * w)%nat, f, 0) = (1 + n, G, 0)).
  rewrite <- (divstep_iter_0 1 R0 (R1 / 2) 1 G (2 * w)) by assumption.
  rewrite <- (divstep_iter_0 1 R0 (R1 / 2) d f n) by assumption.
  rewrite Nat.add_comm. reflexivity. inversion H. assumption. Qed.

(* Compute (repeat 5%Z) 20000%nat. *)

Ltac test_all :=
  repeat match goal with
         | [ H : ?lower <= ?a < ?upper |- _ ] =>
           try lia; destruct (Z.eq_dec a lower) as [e|]; [rewrite e; reflexivity|];
           assert (1 + lower <= a < upper) by lia; clear H
         end; lia.

Fixpoint test_all_fix a bound fuel :=
  match fuel with
  | 0%nat => true
  | S fuel => if (a ^ 2 <? bound) then  test_all_fix (a + 1) bound fuel else false
  end.

Fixpoint old_alg a b n fuel acc bound acc1 acc2 :=
  if (a ^ 2 >=? acc) && (negb (a =? 0)) then (acc,acc1,acc2) else
    match fuel with
    | 0%nat => (-1 ,acc1, acc2)
    | S fuel => match a ^ 2 + b ^ 2 >=? 2 ^ bound with
               | true => if b <=? 0
                        then old_alg a (b + 2) n fuel acc bound acc1 acc2
                        else old_alg (a + 2) (Z.land ((- sqrt (2 ^ (2 * bound) - (a + 2) ^ 2))) (-2)) n fuel acc bound acc1 acc2
               | false => if (fix needs_n_steps d a b n :=
                               match n with
                               | 0%nat => true
                               | S n => if b =? 0 then false else
                                         let '(d', a', b') := divstep d a b in needs_n_steps d' a' b' n
                               end) 1 a (Z.shiftr b 1) n
                         then if (acc =? -1) || (a^2 + b ^2 <=? acc)
                              then old_alg a (b + 2) n fuel (a ^ 2 + b ^ 2) bound a b
                              else old_alg a (b + 2) n fuel acc bound acc1 acc2
                         else old_alg a (b + 2) n fuel acc bound acc1 acc2
               end
    end.

Fixpoint needs_n_steps d a b n :=
  match n with
  | 0%nat => true
  | S n => if b =? 0
          then false
          else let '(d', a', b') := divstep d a b in needs_n_steps d' a' b' n
  end.

(* Fixpoint min_needs_n_list_clever a b fuel := *)
(*   match fuel with *)
(*   | 0 => [] *)
(*           | S fuel  *)

(* Require Import String. *)

(* Local Open Scope string_scope. *)

Fixpoint min_needs_n_steps a b n (acc : Z) fuel :=
  match fuel with
  | 0%nat => -1
  | S fuel =>  if (a ^ 2 >=? acc) && (negb (acc =? -1)%Z)
              then acc
              else if (a ^ 2 + b ^ 2 >=? acc) && (negb (acc =? -1)%Z)
                   then min_needs_n_steps (a + 2) 0 n acc fuel
                   else if needs_n_steps 1 a (b / 2) n || needs_n_steps 1 a ((- b) / 2) n
                        then min_needs_n_steps (a + 2) 0 n
                                               (if (acc =? -1)%Z
                                                then (a ^ 2 + b ^ 2)
                                                else (min (a ^ 2 + b ^ 2) acc)) fuel
                        else min_needs_n_steps a (b + 2) n acc fuel 
  end.

Require Import Program.

Program Fixpoint min_needs_n_steps_nat a b n (acc : Z) fuel {measure fuel (N.lt)} :=
  match fuel with
  | 0%N => -1
  | _ =>  if (a ^ 2 >=? acc) && (negb (acc =? -1)%Z)
              then acc
              else if (a ^ 2 + b ^ 2 >=? acc) && (negb (acc =? -1)%Z)
                   then min_needs_n_steps_nat (a + 2) 0 n acc (N.pred fuel)
                   else if needs_n_steps 1 a (b / 2) n || needs_n_steps 1 a ((- b) / 2) n
                        then min_needs_n_steps_nat (a + 2) 0 n
                                               (if (acc =? -1)%Z
                                                then (a ^ 2 + b ^ 2)
                                                else (min (a ^ 2 + b ^ 2) acc)) (N.pred fuel)
                        else min_needs_n_steps_nat a (b + 2) n acc (N.pred fuel)
  end.

Solve Obligations with try lia.
Next Obligation. exact (Acc_intro_generator (50) ltac:(apply measure_wf; apply N.lt_wf_0)). Defined.

(* Fixpoint enum a b n acc := *)
(*   match n with *)
(*   | 0 => (a, b) *)
(*   | S n => if (a + 2) ^ 2 + b ^ 2 >=? a ^ 2 + (b + 2) ^ 2 *)
(*           then enum (a + 2) 0 *)

Require Import Coq.Numbers.Cyclic.Int63.Int63.
Check int.

Local Open Scope int63.

Definition asr a := set_digit (lsr a 1) 62 (get_digit a 62).

Definition divstep_int (d f g : int) :=
  if (get_digit (opp d) 62) && (negb (is_even g))
  then (1 - d, g, asr (g - f))
  else (1 + d, f, asr (g + (g land 1) * f)).

Fixpoint needs_n_steps_int (d a b : int) n :=
  match n with
  | 0%nat => true
  | S n => if (b == 0)
          then false
          else let '(d', a', b') := divstep_int d a b in needs_n_steps_int d' a' b' n
  end.

Local Coercion to_Z : int >-> Z.
Definition test_needs_n_steps_int d a b n := (needs_n_steps_int d a b n) == (needs_n_steps d a b n).

Definition int_min a b := if a < b then a else b.

Program Fixpoint min_needs_n_steps_nat_int (a b : int) n (acc : int) fuel {measure fuel (N.lt)} :=
  match fuel with
  | 0%N => 1 << 61
  | _ =>  if (leb acc (mul a a))
              then acc
              else if (leb acc (add (mul a a) (mul b b)))
                   then min_needs_n_steps_nat_int (a + 2) 0 n acc (N.pred fuel)
                   else if needs_n_steps_int 1 a (b >> 1) n || needs_n_steps_int 1 a (opp (b >> 1)) n
                        then min_needs_n_steps_nat_int (a + 2) 0 n (int_min (a * a + b * b) acc) (N.pred fuel)
                        else min_needs_n_steps_nat_int a (b + 2) n acc (N.pred fuel)
  end.

Solve Obligations with try lia.
Next Obligation. exact (Acc_intro_generator (50) ltac:(apply measure_wf; apply N.lt_wf_0)). Defined.

Definition bignumber_int:=(min_needs_n_steps_nat_int 1 0 35 (1 << 62) (2 ^ 43)).
Definition bignumber:=(min_needs_n_steps_nat 1 0 30 (-1) (2 ^ 43)).

(* Time Compute min_needs_n_steps_nat_int 1 0 30 (1 << 61) (2 ^ 42). (* 7839829 // 27sec *) *)
(* Time Compute min_needs_n_steps_nat 1 0 30 (-1) (2 ^ 42). (* 7839829 // 255sec *) *)

(* Time Eval vm_compute in min_needs_n_steps_nat 1 0 22 (-1) (2 ^ 22). *)
(* Time Eval native_compute in min_needs_n_steps_nat 1 0 22 (-1) (2 ^ 22). *)

(* Require Import ExtrOcamlIntConv.  (* Should convert coq's numbers to ocaml numbers. *) *)
(* Require Import ExtrOcamlZBigInt. *)
Require Import ExtrOCamlInt63.

(* " NB: The extracted code should be linked with nums.cm(x)a from ocaml's stdlib and with the wrapper big.ml that simplifies the use of Big_int (it can be found in the sources of Coq). " 
https://ocaml.org/releases/4.04/htmlman/libnum.html
*)

(* For precision we should change to Int63 and use 
Requrie Import ExtrOCamlInt63. 
This would also compute faster in Coq, I understand.
 *)

(* Extract Constant Int63.land => "land". *)
(* Extract Constant Int63.lxor => "lxor". *)
(* Extract Constant Int63.lor => "lor". *)

(* Extract Constant Int63.sub => "sub_int". *)
(* Extract Constant Int63.add => "add_int". *)
(* Extract Constant Int63.mul => "mult_int". *)
(* Extract Constant Int63.ltb => "lt_int". *)
(* Extract Constant Int63.leb => "le_int". *)
(* Extract Constant Int63.lsl => "lshift_left". *)
(* Extract Constant Int63.lsr => "lshift_right". *)
(* Extract Constant Int63.eqb => "eq_int". *)
(* Extract Constant Int63.int => "int". *)

(* Extraction "test" bignumber. *)
Extraction "test" bignumber_int.
(* Time Eval native_compute in min_needs_n_steps_nat 1 0 25 (-1) (2 ^ 22). *)

(* Time Compute min_needs_n_steps_nat_alt 1 0 25 (-1) ((2 ^ 30)%N). *)

(* Fixpoint table_maker d a b n table fuel := *)
(*   match fuel with *)
(*   | 0%nat => [(-1,-1)] *)
(*   | S fuel => match table with *)
(*              | [] => if needs_n_steps d a b 0 *)
(*                     then table_maker d a b ((a ^ 2 + b ^ 2, 0)) *)
(*                                      else table_maker  *)
(*                                   |  *)


(* Compute min_needs_n_steps 1 (Z.land (- sqrt (2 ^ 30 - 1 ^ 2)) (-2)) 6 (2 ^ 30) (-1) 15 0 0. *)
  
(* Fixpoint enum_all a b l divstep_fuel fuel := *)
(*   match fuel with *)
(*   | 0%nat => [] *)
(*   | S fuel => match a ^ 2 + b ^ 2 >=? 2 ^ 42 with *)
(*           | true => enum_all (a + 1) 0 l divstep_fuel fuel *)
(*           | false => (fix divstep_needed a b fuel := *)
(*                        match fuel with *)
(*                        | 0%nat => [(0, 0)] *)
(*                     | S fuel => ) *)

(* Local Notation b := ((log2 (sqrt (R0 ^ 2 + R1 ^ 2)))). *)

(* Theorem G4 : exists x y, divstep_iter 1 R0 (R1 / 2) (19 * b / 17) = (x, y, 0). *)
(* Proof. Admitted. *)

(* Notation it := (if b <=? 21 *)
(*                  then 19 * b / 7 *)
(*                  else if b <=? 46 *)
(*                       then (49 * b + 23) / 17 *)
(*                       else 49 * b). *)

(* Theorem G6 : exists x y, divstep_iter 1 R0 (R1 / 2) (to_nat it) = (x, y, 0). *)
(* Proof. *)
(*   destruct (le_dec b 21). *)

(*   assert (H : b <=? 21 = true) by (apply Z.leb_le; apply Z2Nat.inj_le; lia); rewrite H. apply G4. *)
  
  
