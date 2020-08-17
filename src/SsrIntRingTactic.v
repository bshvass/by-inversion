From mathcomp Require Export all_ssreflect.
From mathcomp Require Export all_algebra.

Local Open Scope ring_scope.
Local Open Scope int_scope.

Export intRing.
Export intZmod.

Lemma int_ring : @ring_theory int
                              0
                              1
                              addz
                              mulz
                              (fun n m => n - m)
                              oppz
                              (@eq _).
Proof. split;
       [exact add0z |
        exact addzC |
        exact addzA |
        exact mul1z |
        exact mulzC |
        exact mulzA |
        exact mulz_addl |
        by [] |
        move=> x; rewrite addzC; apply addNz]. Qed.       

Local Close Scope ring_scope.
Local Close Scope int_scope.

From Coq Require Import ZArith.
Import BinIntDef.

Open Scope Z_scope.

Definition int_of_Z (z : Z) :=
  match z with
  | Z0 => Posz 0
  | Zpos p => Posz (nat_of_pos p)
  | Zneg p => Negz ((nat_of_pos p).-1)
  end.

Open Scope positive_scope.

Lemma pos_to_nat_corr p : Pos.to_nat p = nat_of_pos p.
Proof. elim: p => [p IH | p IH | ] //=. 
         by rewrite natTrecE -IH Pos2Nat.inj_xI -mul2n.
         by rewrite natTrecE -IH Pos2Nat.inj_xO -mul2n. Qed.

Lemma nat_of_pos_Sn p : exists n, nat_of_pos p = n.+1.
Proof.
  case H: (nat_of_pos p).
  - by move: H (Pos2Nat.is_pos p); rewrite -pos_to_nat_corr => -> /Nat.lt_irrefl //.
  - by eexists. Qed.

Lemma nat_of_sub_pos p q : p < q -> nat_of_pos (q - p) = (nat_of_pos q - nat_of_pos p)%nat.
Proof.
  move=> H; by rewrite -!pos_to_nat_corr Pos2Nat.inj_sub. Qed.    

Close Scope positive_scope.

Import GRing.

Lemma minus_par (x y : int) : (- ( x + y ))%R = (- x  - y)%R.
Proof. by rewrite -[y]opprK opp_is_additive. Qed.

Lemma int_of_add_Z x y : int_of_Z ( x + y ) = ((int_of_Z x) + (int_of_Z y))%R.
Proof.
  case x; case y; move=> //=; move=> p.
  - by rewrite add0r. 
  - by rewrite addr0.
  - by (move=> q; rewrite nat_of_add_pos). 
  - move=> q; move: (nat_of_pos_Sn p) => [n] H1; case: (Pos.lt_total q p); case => H.
    + rewrite Z.pos_sub_lt //= (nat_of_sub_pos q p H)
              !NegzE H1 -pred_Sn subSKn -subSn.
      apply oppr_inj; rewrite opprK minus_par -subzn /GRing.opp /=. 
      by rewrite oppzK addrC.
      by rewrite -H1; apply: ltnW; apply /ltP; rewrite -!pos_to_nat_corr; apply /Pos2Nat.inj_lt. 
      by rewrite -ltnS -H1; apply /ltP; rewrite -!pos_to_nat_corr; apply /Pos2Nat.inj_lt. 
    + by rewrite H Z.pos_sub_diag /= H1 -pred_Sn NegzE /GRing.add /= ltnSn subnn.
    + rewrite Z.pos_sub_gt //= nat_of_sub_pos // H1 -pred_Sn NegzE -H1 subzn //. 
      by apply /ltnW; apply /ltP; rewrite -!pos_to_nat_corr; apply /Pos2Nat.inj_lt. 
  - by rewrite addr0.
  - move=> q;
    move: (nat_of_pos_Sn p) => [n] H1;
    move: (nat_of_pos_Sn q) => [m] H2; 
    case: (Pos.lt_total q p); case => H.
    + rewrite Z.pos_sub_gt // H2 /= nat_of_sub_pos // NegzE -H2 -subzn.
      by rewrite addrC. 
      by apply /ltnW; apply /ltP; rewrite -!pos_to_nat_corr; apply /Pos2Nat.inj_lt. 
    + by rewrite H H1 Z.pos_sub_diag /= NegzE /GRing.add /= ltnSn subnn.
    + rewrite Z.pos_sub_lt //= (nat_of_sub_pos p q H) !NegzE H2 /= subSKn -subSn.
      apply oppr_inj; rewrite opprK minus_par -subzn /GRing.opp /=.
      by rewrite oppzK addrC.
      by rewrite -H2; apply: ltnW; apply /ltP; rewrite -!pos_to_nat_corr; apply /Pos2Nat.inj_lt. 
      by rewrite -ltnS -H2; apply /ltP; rewrite -!pos_to_nat_corr; apply /Pos2Nat.inj_lt. 
  - move=> q; rewrite nat_of_add_pos; move: (nat_of_pos_Sn p) => [n] ->;
    move: (nat_of_pos_Sn q) => [m] ->; by rewrite /GRing.add /= -addnS. Qed.  

Lemma int_of_opp_Z x : int_of_Z (- x) = (- int_of_Z x)%R.
Proof.
  case: x => // p /=; move: (nat_of_pos_Sn p) => [n] -> //=. Qed.  

(* Lemma oppz_inj x y : oppz x = oppz y -> x = y. *)
(* Proof. *)
(*   move=> /(f_equal oppz). by rewrite !oppzK. Qed. *)

Lemma int_of_mul_Z x y : int_of_Z (x * y) = (int_of_Z x * int_of_Z y)%R.
Proof.
  case: x => [|p /=|p /=].
  - by rewrite Z.mul_0_l mul0r.
  - case: y => [|q /=|q /=].
    + by rewrite mulr0.
    + by rewrite nat_of_mul_pos.
    + by rewrite nat_of_mul_pos;
      move: (nat_of_pos_Sn q) => [n] ->; move: (nat_of_pos_Sn p) => [m] -> //=.
  - case: y => [|q /=|q /=].
    + by rewrite mulr0.
    + by rewrite nat_of_mul_pos;
      move: (nat_of_pos_Sn q) => [n] -> //=; move: (nat_of_pos_Sn p) => [m] ->;
      rewrite !NegzE; apply /f_equal;
      rewrite -pred_Sn -(S_pred (m.+1 * n.+1) 0) mulnC //; apply /ltP. 
    + by rewrite nat_of_mul_pos; move: (nat_of_pos_Sn q) => [n] ->; move: (nat_of_pos_Sn p) => [m] -> //. Qed.
      
Lemma int_morph :
  ring_morph (Posz 0) (Posz 1) addz mulz (fun x y => (x - y)%R) oppz (@eq _) 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb int_of_Z.
Proof.
  split; rewrite //=.
  - exact int_of_add_Z.
  - move=> x y. by rewrite -Z.add_opp_r int_of_add_Z int_of_opp_Z.
  - exact int_of_mul_Z.
  - exact int_of_opp_Z.
  - by move=> x y /Z.eqb_spec ->. Qed.  

Close Scope Z_scope.

Open Scope ring_scope.
Open Scope int_scope.

Definition Z_of_int i :=
  match i with
  | Posz n => match n with
              | 0%nat => Z0
              | n.+1 => Zpos (pos_of_nat n.+1 n.+2)
              end
  | Negz n => Zneg (pos_of_nat n.+1 n.+2)
  end.

Fixpoint pop_succn e := if e is e'.+1 then fun n => pop_succn e' n.+1 else id.

Ltac pop_succn e := eval lazy beta iota delta [pop_succn] in (pop_succn e 1).

Ltac int_litteral e :=
  match e with
  | Posz ?e' => (* constr: (Z_of_int e') *)
                         
                         match pop_succn e' with
                         | ?n.+1 => constr: (Z_of_int e)
                         | _ => NotConstant
                         end 
                         
  | Negz ?e' => (* constr: (Z_of_int e') *)
                         
                         match pop_succn e' with
                         | ?n.+1 => constr: (Z_of_int e)
                         | _ => NotConstant
                         end
                         
  | _ => NotConstant
  end.

Add Ring int_ring_ssr_2 : int_ring (morphism int_morph,
                                    constants [int_litteral],
                                    preprocess [succn_to_add; rewrite ?PoszD]).

Arguments addz m n : simpl never.
Arguments mulz m n : simpl never.

Ltac intunfold := rewrite /exprz /GRing.exp; simpl; rewrite /GRing.add /GRing.mul /GRing.opp /GRing.one /GRing.zero; simpl.

Ltac intring := intunfold; ring.
Ltac intring_simplify := intunfold; ring_simplify.

Open Scope ring_scope.
Open Scope int_scope.

Lemma intringtest (x y : int) : 3%:Z *x + x + y - (x + y)* 5%:Z = (-x) - x + x - 7%:Z *y + y*3.
Proof. intring_simplify. by []. Qed.

Lemma intringsimpltest (x y : int) : 3%:Z *x + x + y - (x + y)* 5%:Z = (-x) - x + x - 7%:Z *y + y*3.
Proof. intunfold. intring_simplify. by []. Qed.

Check Posz.

Close Scope ring_scope.
Lemma testtest (n : int) (m : nat) : (`|n|) * m = m * (`|n|).
Proof. ring_simplify. ring. Qed.
Open Scope ring_scope.
  
Lemma natinttest (n m : nat) : n%:Z * m = m%:Z * n.
Proof. intring. Qed.

Lemma intnat_test (k : nat) (x : int) : 2%:Z * x - x + k = x + 2%:Z * k%:Z - k%:Z. 
Proof. intring. Qed.

Lemma succntoadd (n m : nat) (z : int) : (n.+1.+2.+3.+2)%:Z = n.+3%:Z + 2.+3%:Z.
Proof. intring. Qed.

Lemma succntoadd_nat (n m : nat) : n.+2 = (n.+1 + 1)%nat.
Proof. intring. Qed.

Lemma succntoadd_Z (n m : nat) : n.+2%:Z = n.+1%:Z + 1.
Proof. intring. Qed.

Lemma succntoadd_Z2 (n m : nat) (x : int) : n.+2%:Z * x = x*(n.+1%:Z + 1).
Proof. intring. Qed.

Lemma exptest (x y : int) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + x * y * 2.
Proof. intring. Qed.

Require Import Coq.micromega.Lia.

Lemma Ztest (x y : Z) : (x^2 + y = y + x * x)%Z.
Proof. lia. Qed.
