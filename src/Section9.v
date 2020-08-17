From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
(* From mathcomp Require Import ssrint. *)
From BY Require Import SsrIntRingTactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module withOwnMatMult.

Open Scope ring_scope.
Open Scope int_scope.

Record matrix := Matrix { a11 : int; a12 : int; a21 : int; a22 : int }.

Record colold := Col { a1 : int ; a2 : int }.

Definition col := (int * int)%type.
Notation "[ a , b ; c , d ]" := (Matrix a b c d).
Notation "[ a ; b ]" := (@pair int int a b).

Definition I := [ 1 , 0 ; 0 , 1 ].

Compute [ 4 ; 5 ] *~ 2.

Search _ (_ * _ -> _ -> _ * _).

Definition matmult m1 m2 := [ (a11 m1)*(a11 m2) + (a12 m1)*(a21 m2) ,
                              (a11 m1)*(a12 m2) + (a12 m1)*(a22 m2) ;
                              (a21 m1)*(a11 m2) + (a22 m1)*(a21 m2) ,
                              (a21 m1)*(a12 m2) + (a22 m1)*(a22 m2) ].  
Definition colmult m c := [ (a11 m)*(c.1) + (a12 m)*(c.2) ;
                            (a21 m)*(c.1) + (a22 m)*(c.2) ].
Definition colscale c s := c * [ s ; s ].

Notation "c ** s" := (colscale c s) (at level 30).
Notation "m *col c" := (colmult m c) (at level 45).
Notation "m *mat n" := (matmult m n) (at level 40).

(* Definition eqcol c1 c2 := ((a1 c1) == (a1 c2)) && ((a2 c1) == (a2 c2)). 

Theorem eqcolP : Equality.axiom eqcol.
Proof.
  move=> c1 c2. apply: (iffP idP) => [|<-]. case: c1 => [ a1 a2 ]. case: c2 => [ a3 a4 ]. rewrite /eqcol /=.
  move=> /andP. by case=> /eqP -> /eqP ->.
  rewrite /eqcol. case: c1 => /= a b. by rewrite !eq_refl. Qed. 

Definition col_eqMixin := Equality.Mixin eqcolP.
Canonical col_eqType := @Equality.Pack col col_eqMixin. *)

Definition eqmat m1 m2 := (a11 m1 == a11 m2) && (a12 m1 == a12 m2) && (a21 m1 == a21 m2) && (a22 m1 == a22 m2).

Theorem eqmatP : Equality.axiom eqmat.
Proof.
  move=> c1 c2; apply (iffP idP) => [ | ]. rewrite /eqmat. case: c1. case: c2 => a b c d e f g h /= /andP.
  case. move=> /andP. case. move=> /andP. case. by repeat case=> /eqP ->.
  rewrite /eqmat => ->. by rewrite !eq_refl. Qed.

Definition mat_eqMixin := Equality.Mixin eqmatP.
Canonical mat_eqType := @Equality.Pack matrix mat_eqMixin.


Definition oddz n := odd `|n|%N.


Definition Tmat (d f g : int) := 
                                 let b := (0 < d) && (oddz g) in
                                 if b then
                                   [ 0 , 2 ; -1 , 1 ]
                                 else
                                   [ 2 , 0 ; modz g 2 , 1 ].

Definition Smat (d f g : int) :=
                                 let b := (0 < d) && (oddz g) in
                                 if b then
                                   [ 1 , 0 ; 1 , -1 ]
                                 else
                                   [ 1 , 0 ; 1 , 1 ].

Definition divstep d f g : int * int * int := if (0 < d) && (oddz g)
                                        then (1 - d, g, divz (g - f) 2 )
                                        else (1 + d, f, divz (g + (modz g 2) * f) 2).

Fixpoint divstepn d f g n :=
  match n with
  | 0 => (d, f, g)
  | S n => divstep (divstepn d f g n).1.1 (divstepn d f g n).1.2 (divstepn d f g n).2
  end.

Definition dn d f g n := (divstepn d f g n).1.1.
Definition fn d f g n := (divstepn d f g n).1.2.
Definition gn d f g n := (divstepn d f g n).2.

Lemma divstep1 d f g : divstep d f g = divstepn d f g 1.
Proof. by []. Qed.

Definition Tn d f g n := Tmat (dn d f g n) (fn d f g n) (gn d f g n).
Definition Sn d f g n := Smat (dn d f g n) (fn d f g n) (gn d f g n).

Lemma dvdz_add : forall (n m k : int), n %| m -> n %| k -> n %| m + k. 
Proof.
    move=> n m k /dvdzP [p -> /dvdzP [q ->]]. apply/dvdzP. exists (p + q). by rewrite GRing.Theory.mulrDl. Qed.

Lemma oddz_opp n : oddz n = oddz (- n).
Proof.
  by rewrite /oddz abszN. Qed.

Close Scope ring_scope.

Lemma oddP n : reflect (exists q, n = 2 * q + 1) (odd n).
  apply/(iffP idP).
    move: (leqnn n). move: {-2}n. elim: n  => [ | n IH]; first by case.
    case=> [//|]. case. by exists 0.
    move=> n0 /ltnW leq /= /negbNE odd. move: (IH n0 leq odd) => [q] H. exists (q + 1).
    by rewrite H -addn2 mulnDr muln1 !addn1 !addn2.
    move=> [p -> {n}]. by rewrite odd_add mul2n odd_double. Qed.

Open Scope ring_scope.

Import intOrdered.
Import Num.Theory.
Import Num.Def.
Import GRing.
Import GRing.Theory.

Lemma minus_par (x y : int) : - (x + y) = - x - y.
Proof. by rewrite -[y]opprK opp_is_additive. Qed.

Lemma lemma_1 (n : int) : 0 <= n <-> 0 <= 2%:Z * n + 1 .
Proof.
  split. move=> H. suff: 0 <= 2%:Z * n. move=> H1. apply: Num.Theory.addr_ge0. exact H1. by [].
  apply: Num.Theory.mulr_ge0. by []. exact H. case: n => [// | ]. move=> n. rewrite NegzE. rewrite !intS !mulrDl.
    by []. Qed.

Import mc_1_10.Num.Theory.

Lemma lemma_1_inv (n : int) : n < 0 <-> 2%:Z * n + 1 < 0.
Proof.
  split; apply: contraTT; rewrite -!lerNgt; apply lemma_1. Qed.

Locate "!=".

Lemma neq_lez_ltz (n m : int) : n != m -> n <= m -> n < m.
move=> nneqm. rewrite ler_eqVlt => /orP. case=> [ /eqP H | // ]. move: H nneqm => ->. by rewrite eq_refl. Qed.

Lemma oddzexisP_lemma (n : int) : 0 <= n -> (exists (q : int), n = 2%:Z * q + 1) -> oddz n.
  move=> nge0 [q] H. rewrite /oddz. apply/oddP. 
  exists `|q|%N. have: 0 <= q. apply lemma_1. have: n <= 2%:Z * q + 1.
  rewrite ler_eqVlt. apply/orP; left. apply/eqP. exact H. apply (ler_trans nge0).
  move: q H nge0. case. case n. move=> n1 q. move=> H H1 H2. rewrite H. by []. by []. by []. Qed.
  
Lemma oddzexisP (n : int) : reflect (exists (q : int), n = 2%:Z * q + 1) (oddz n).
  apply/(iffP idP). rewrite /oddz => /oddP. case/orP: (intOrdered.lez_total 0 n) => /= H [q] H1.
  rewrite -(gez0_abs H) H1. by exists q%:Z.
  exists (- q%:Z - 1). apply GRing.oppr_inj.
  by rewrite -(lez0_abs H) H1 minus_par mulrDr minus_par 2!mulrN 2!opprK mulr1 -addrA.
  case/orP: (ler_total 0 n). apply oddzexisP_lemma.
  move=> nle0. have: 0 <= -n. rewrite -oppr_le0 opprK. exact nle0.
  move=> oppnge0 [q] H. rewrite oddz_opp. have: exists q :int, -n = 2%:Z*q +1. exists (-q -1). 
  rewrite H mulrDr mulrN1 mulrN -addrA. have: - (2%:Z) + 1 = -1 by []. move=> ->. by rewrite minus_par.
  move: oppnge0. apply oddzexisP_lemma. Qed.

Open Scope int_scope.
  
Lemma fodd_f1odd : forall d f g, oddz f -> oddz (fn d f g 1). 
Proof.
  move=> d f g fodd. rewrite /fn /= /divstep. case H: ((0 < d) && oddz g) => /=. move: H => /andP.
    by case. exact fodd. Qed.

Lemma fodd_fnodd d f g n : oddz f -> oddz (fn d f g n).
  elim: n => [//| n IH H] /=. rewrite /fn /= /divstep.
  case H2: ((0 < (divstepn d f g n).1.1) && (oddz (divstepn d f g n).2)) => /=. move: H2. by case/andP.
  apply: IH. exact H. Qed.

Lemma oddzmod2 n : oddz n -> n %% 2 = 1.
Proof.
  move=> /oddzexisP [q] ->. rewrite /modz divzDl. rewrite mulKz.
    by rewrite mulrDl minus_par addrA -[_ + 1 - _](addrA) [1 - _](addrC) addrA mulrC addrN add0r.
    by []. by apply dvdz_mulr. Qed.

Lemma noddzdvdzP n : reflect (2 %| n) (~~ oddz n).
Proof.
  apply/(iffP idP). by rewrite /oddz dvdzE /= dvdn2.
  rewrite /oddz. move=> /dvdzP [q] ->. by rewrite abszM muln2 odd_double. Qed.    

Lemma noddzmod2 n : ~~ oddz n -> n %% 2 = 0.
Proof. move=> /noddzdvdzP /dvdzP [q ->]. by apply modzMl. Qed.

Lemma oddz_add_lemma1 n m : oddz n -> ~~ oddz m -> oddz (n + m).
Proof.
  move=> /oddzexisP [q ->] /noddzdvdzP /dvdzP [p ->].
  rewrite -addrA [1 + _](addrC) addrA mulrC -mulrDl /oddz mulrC.
  apply/oddzexisP. by exists (q + p). Qed.

Lemma oddz_add_lemma2 n m : oddz n -> oddz m -> ~~ oddz (n + m).
Proof.
  move=> /oddzexisP [q ->] /oddzexisP [p ->].
  rewrite addrA -[_ + 1 + _](addrA) [1 + _](addrC) addrA -mulrDr -addrA -intS -{2}[2%:Z](mulr1).
    by rewrite -mulrDr /oddz abszM /= mul2n odd_double. Qed.

Lemma oddz_add_lemma3 n m : ~~ oddz n -> ~~ oddz m -> ~~ oddz (n + m).
Proof.
  move=> /noddzdvdzP /dvdzP [p ->] /noddzdvdzP /dvdzP [q ->].
  by rewrite -mulrDl /oddz abszM /= muln2 odd_double. Qed.

Print negb.

Lemma oddz_add n m : oddz (n + m) = oddz n (+) oddz m.
Proof.
  case: (oddz n)/idP; case: (oddz m)/idP.
  - move=> oddm oddn. apply/negb_inj. by rewrite oddz_add_lemma2.
  - move=> /idP noddm oddn. by rewrite oddz_add_lemma1.
  - rewrite addrC. move=> oddm /idP noddn. by rewrite oddz_add_lemma1.
  - move=> /idP noddm /idP noddn. apply/negb_inj. by rewrite oddz_add_lemma3. Qed.

Lemma oddz_mul_lemma1 n m : oddz n -> ~~ oddz m -> ~~ oddz (n * m).
Proof.
  move=> /oddzexisP [q ->] /noddzdvdzP /dvdzP [p ->].
  apply/noddzdvdzP. apply/dvdzP. exists (2%:Z * q * p + p). intring. Qed.

Lemma oddz_mul_lemma2 n m : oddz n -> oddz m -> oddz (n * m).
Proof.
  move=> /oddzexisP [q ->] /oddzexisP [p ->].
  apply/oddzexisP. exists (2%:Z * q * p + p + q). intring. Qed.

Lemma oddz_mul_lemma3 n m : ~~ oddz n -> ~~ oddz m -> ~~ oddz (n * m).
Proof.
  move=> /noddzdvdzP /dvdzP [p ->] /noddzdvdzP /dvdzP [q ->].
  apply/noddzdvdzP. apply/dvdzP. exists (p * q * 2). intring. Qed.

Lemma oddz_mul n m : oddz (n * m) = oddz (n) && oddz (m).
Proof.
  case: (oddz n)/idP => [oddn|/negP noddn]; case: (oddz m)/idP => [oddm|/negP noddm].
    by rewrite oddz_mul_lemma2.
    apply negb_inj. by rewrite oddz_mul_lemma1. 
    apply negb_inj. by rewrite mulrC (oddz_mul_lemma1 oddm noddn).
    apply negb_inj. by rewrite oddz_mul_lemma3. Qed.
  
(*
Notation "\mmul_ ( i <- r | P ) F" :=
  (\big[matmult / I]_(i <- r | P%B) F%N) (at level 50). *)

(* Notation "\mmul_ ( m <= i < n ) F" :=
  (\big[matmult / I]_(m <= i < n) F) (at level 50). *)

Search (_ = _.+1).

Search (Monoid.law).

Print Equality.axiom.
Print Monoid.law.


Ltac entrywise :=
        apply: eqmatP; rewrite /eqmat;
        apply /andP; split;
                       [ apply /andP; split;
                         [ apply /andP; split;
                           apply /eqP => //=
                         | apply /eqP => //=]
                       | apply /eqP => //=].

Ltac entrywise_col :=
        apply: eqP;
        apply /andP; split; apply /eqP => //=.

Ltac folddefs := rewrite -!/(dn _ _ _ _) -!/(fn _ _ _ _) -!/(gn _ _ _ _).

Theorem mulmAlemma A B C : matmult (matmult A B) C = matmult A (matmult B C).
Proof.
Hint Resolve mulrA mulrC addrA addrC mulrDl mulrDr.
  case: A => a1 a2 a3 a4. case: B => b1 b2 b3 b4. case: C => c1 c2 c3 c4.
  rewrite /matmult /=. entrywise; intring. Qed.

Theorem mymulmA : associative matmult.
Proof.
  rewrite /associative => A B C. by rewrite mulmAlemma. Qed.

Theorem mymulIm : left_id I matmult.
Proof.
  rewrite /left_id /matmult /I /=. case=> a b c d. entrywise; intring. Qed.

Theorem mymulmI : right_id I matmult.
Proof.
  rewrite /left_id /matmult /I /=. case=> a b c d. entrywise; intring. Qed.

Theorem matmult_act_on_col A B v : (A *mat B) *col v = A *col (B *col v).
Proof.
  case: A => a1 a2 a3 a4. case: B => b1 b2 b3 b4. case: v => v1 v2.
  rewrite /matmult /colmult /=. entrywise_col; intring. Qed.

Theorem colmult_act_on_scale A v s : (A *col v) ** s = A *col (v ** s).
Proof.
  case A=> a b c d. case v=> v1 v2. rewrite /colscale /colmult /=. entrywise_col; intring. Qed.

Theorem colscale_act_on_mul v s1 s2 : (v ** s1) ** s2 = v ** (s1 * s2). 
Proof.
  case v=> v1 v2. rewrite /colscale /=. entrywise_col; intring. Qed.
  
Theorem mulcI c : I *col c = c.
Proof.
  case: c => c1 c2. entrywise_col; intring. Qed.

Theorem mulc1 c : c ** 1 = c.
Proof. case c=> c1 c2. entrywise_col; intring. Qed.
  
Import Monoid.
Canonical mmul_monoid := Law mymulmA mymulIm mymulmI.

Search _ ((_ <= _)%N).
Locate "_ ^+ _".

Check exp.

Lemma induction_lemma (m k : nat) : (m <= k)%N -> exists t, k = (m + t)%N.
Proof.
  elim: m k => [| m IH].
  - move=> k H{H}. eexists. by rewrite add0n.
  - move=> k mltk. have: (m <= k)%N. apply /ltnW; exact mltk. move=> /IH [q].
    case: q=> [|q ->]. rewrite addn0 => contra. move: contra mltk => ->. by rewrite ltnn.
    eexists. by ring_simplify. Qed.

Lemma strong_induction (P : nat -> Prop) : P 0%N ->  (forall n, ((forall k, (k < n.+1)%N -> P k) -> P n.+1)) -> forall n, P n.
Proof.
  move=> P0 IH n. elim: n {-2}n (leqnn n) => [n|n IH2 m].
  - by rewrite leqn0 => /eqP ->.
  - rewrite leq_eqVlt => /orP [/eqP ->|].
    + apply IH. apply IH2.
    + apply IH2. Qed.

Lemma strong_induction_from_m (m : nat) (P : nat -> Prop) : (forall n, (n < m)%N -> P n) ->
                                  P m ->
                                  (forall n, (m < n)%N -> ((forall l, (l < n)%N -> P l) -> P n)) ->
                                  (forall n, P n).
Proof.
  move=> Psmall Pm IH k. case H: (m <= k)%N.
  - have: exists t, k = (m + t)%N by apply induction_lemma. move=> [q] ->.
    elim/strong_induction: q => [|q IH2]. by rewrite addn0.
    apply IH. by rewrite addnS ltnS leq_addr.
    move=> l llemSq. case/orP: (leq_total l m).
    + rewrite leq_eqVlt => /orP [/eqP -> //|]. by apply Psmall.
    + rewrite leq_eqVlt => /orP [/eqP /esym -> //|]. move=> mltl.
      move: mltl llemSq => /induction_lemma [t] ->. rewrite addSn -addnS. rewrite ltn_add2l. apply IH2.
  - move: H. move=> /idP /negP. rewrite -ltnNge. apply Psmall. Qed.
  
Lemma induction_from_m (m : nat) (P : nat -> Prop) : (forall n, (n < m)%N -> P n) ->
                                  P m ->
                                  (forall n, (m < n.+1)%N -> (P n -> P n.+1)) ->
                                  (forall n, P n).
Proof.
  move=> Psmall Pm IH k. case H: (m <= k)%N.
  - have: exists t, k = (m + t)%N by apply induction_lemma. move=> [q] ->.
    elim: q => [|q IH2].
    + by rewrite addn0.
    + rewrite addnS. apply IH.
      * by rewrite ltnS leq_addr.
      * by [].
  - move: H. move=> /idP /negP. rewrite -ltnNge. apply Psmall. Qed.

Lemma Tn_transition : forall d f g m, oddz f ->
    [ fn d f g m.+1 ; gn d f g m.+1 ] ** 2%Z = ((Tn d f g m) *col [ fn d f g m ; gn d f g m ]).
Proof.
  move=> d f g m /(fodd_fnodd d g m) fmodd. rewrite /fn /gn /colmult /= /Tn /Tmat /divstep /=.
  case H: ((0 < (divstepn d f g m).1.1) && (oddz (divstepn d f g m).2)) => /=. 
  entrywise_col. intring.
  rewrite divzK. intring. 
  apply/noddzdvdzP. rewrite oddz_add -oddz_opp. move/andP: H. case=> H ->. by rewrite fmodd.
  case: (oddz (divstepn d f g m).2)/idP => [H1| /negP H1].
  entrywise_col. intring.
  rewrite (oddzmod2 H1) mul1r divzK. intring.
  apply/noddzdvdzP. by rewrite oddz_add fmodd H1.
  entrywise_col. intring. 
  rewrite (noddzmod2 H1) mul0r add0r addr0 divzK. intring.
  apply/noddzdvdzP. exact H1. Qed.

Lemma Sn_transition d f g m :
    [ 1 ; dn d f g m.+1 ] = (Sn d f g m) *col [ 1 ; dn d f g m ].
Proof.
  rewrite /dn /Sn /Smat /colmult /= /divstep; folddefs.
  case: ((0 < dn d f g m) && oddz (gn d f g m)); entrywise_col; intring. Qed.

Section _9.

Theorem _9_1_1 d f g (n m : nat) : (m <= n)%N -> oddz f ->
    [ fn d f g n ; gn d f g n ]** 2%:Z ^+ (n - m) =
    (\big[matmult / I]_(m <= i < n) Tn d f g (n + m - i.+1)) *col [ fn d f g m ; gn d f g m ].
Proof.
  elim: n m => [m | n IH m]. rewrite leqn0 => /eqP -> /=.
  rewrite big_nat big_geq //. by rewrite sub0n expr0 mulc1 mulcI.
  rewrite (leq_eqVlt m n.+1) => /orP [ eq | ltq ]. move: eq => /eqP ->.
  rewrite big_nat big_geq //=. by rewrite subnn expr0 mulc1 mulcI.
  move: ltq. rewrite ltnS. move=> mleqn fodd. rewrite big_nat_recl //.
  have: forall i, (m <= i < n)%N -> (Tn d f g (n.+1 + m - i.+2) = Tn d f g (n + m - i.+1)).
  move=> i H. by rewrite addnC -addn1 addnA  -[ i.+2 ](addn1) subnDA subnAC -addnBA // subnn addn0 addnC.
  move=> H. rewrite (eq_big_nat I matmult H). rewrite matmult_act_on_col -IH //.
  have: (n.+1 + m - m.+1 = n)%N. rewrite -addn1 -addnA [(1 + m)%N]addnC -addnBA addn1 -[m.+1]addn1.
  rewrite subnDA subnAC -addnBA //. by rewrite subnn addn0 subnn addn0. by apply leqnn.
  move=> ->. rewrite -colmult_act_on_scale -Tn_transition //.
  rewrite colscale_act_on_mul /=. by rewrite -exprS subSn. Qed.

Theorem _9_1_2 d f g (n m : nat) : (m <= n)%N -> oddz f ->
    [ 1 ; dn d f g n  ] =
    (\big[matmult / I]_(m <= i < n) Sn d f g (n + m - i.+1)) *col [ 1 ; dn d f g m ].
Proof.
  elim/(@induction_from_m m): n => [n c1 c2 | H{H} | n mltSn IH mleSn{mleSn}] fodd.
  - move: (leq_ltn_trans c2 c1). by rewrite ltnn.
  - rewrite big_nat big_geq //. rewrite /dn /I /colmult /=. entrywise_col; intring.
  - rewrite big_nat_recl; [ | by rewrite -ltnS].
    have: forall i, (m <= i < n)%N -> (Sn d f g (n.+1 + m - i.+2) = Sn d f g (n + m - i.+1)).
    move=> i H. by rewrite addnC -addn1 addnA  -[ i.+2 ](addn1) subnDA subnAC -addnBA // subnn addn0 addnC.
    move=> H. rewrite (eq_big_nat I matmult H) {H}. rewrite matmult_act_on_col -IH //.
    have: (n.+1 + m - m.+1 = n)%N. rewrite -addn1 -addnA [(1 + m)%N]addnC -addnBA addn1 -[m.+1]addn1.
    rewrite subnDA subnAC -addnBA //. by rewrite subnn addn0 subnn addn0. by apply leqnn. move=> -> /=.
    by rewrite -Sn_transition. Qed.

Theorem _9_2 (d f g : int) (n m : nat) : oddz f -> (m < n)%N -> exists x y v w : int,
                             \big[matmult / I]_(m <= i < n) Tn d f g (n + m - i.+1) =
                             [ x * 2 , y * 2 ; v , w ].
Proof.
  case: n => [ // | n ] fodd. elim: n => [ | n IH]. rewrite ltnS leqn0 => /eqP ->.
  rewrite big_nat1 addn0 subnn /Tn /Tmat /divstepn /=.
  case: ((0 < d) && oddz g).
  exists 0; exists 1; exists (-1); exists 1. by rewrite mul0r mul1r.
  exists 1; exists 0; exists (g %% 2)%Z; exists 1. by rewrite mul0r mul1r.
  rewrite ltnS leq_eqVlt; case/orP => [ /eqP -> | mleSn ].
  - rewrite big_nat1.
    rewrite addnC -addnBA // -2!addn2 add0n. rewrite subnDr subnn addn0.
    rewrite /Tn /Tmat.
    case: ((0 < (divstepn d f g n.+1).1.1) && oddz (divstepn d f g n.+1).2).
    exists 0; exists 1; exists (-1); exists 1. by rewrite mul0r mul1r.
    exists 1; exists 0; exists ((divstepn d f g n.+1).2 %% 2)%Z; exists 1. by rewrite mul0r mul1r.
  - rewrite big_nat_recl; last (rewrite ltnW //; exact mleSn).
    have: forall i, (m <= i < n.+1)%N -> (Tn d f g (n.+2 + m - i.+2) = Tn d f g (n.+1 + m - i.+1)).
    move=> i H. by rewrite addnC -addn1 addnA  -[ i.+2 ](addn1) subnDA subnAC -addnBA // subnn addn0 addnC.
    move=> H. rewrite (eq_big_nat I matmult H){H}.
    move: mleSn => /IH [ x' [ y' [ v' [ w' ]]]] ->.
    rewrite -addn1 -addnA [ (1 + m)%N ]addnC addn1 -addnBA // subSS subnn addn0.
    rewrite /Tn /Tmat.
    case: ((0 < (divstepn d f g n.+1).1.1) && oddz (divstepn d f g n.+1).2).
    rewrite /matmult /= !mul0r !add0r.
    exists v'; exists w'; exists (-1 * (x' * 2) + 1 * v'); exists (-1 * (y' * 2) + 1 * w').
    by rewrite [ 2%:Z * v' ]mulrC [ 2%:Z * w' ]mulrC.
    rewrite /matmult /= !mul0r !addr0 !mul1r 2!mulrA.
    by exists (2%:Z * x'); exists (2%:Z * y');
    exists (((divstep (divstepn d f g n).1.1 (divstepn d f g n).1.2 (divstepn d f g n).2).2 %% 2)%Z * (x' * 2) + v');
    exists (((divstep (divstepn d f g n).1.1 (divstepn d f g n).1.2 (divstepn d f g n).2).2 %% 2)%Z * (y' * 2) + w'). Qed.

Lemma addzSn n : n.+1%:Z = n%:Z + 1.
Proof. by rewrite -addn1. Qed.

Lemma addzSSn n : n.+2%:Z = n%:Z + 2.
Proof. by rewrite -addn2. Qed.


Theorem _9_3 (d f g : int) (n m : nat) : (m < n)%N -> (exists k : nat, (k <= n - m - 1)%N /\ 
    \big[matmult / I]_(m <= i < n) Sn d f g (n + m - i.+1) =
     [ 1, 0; n%:Z - m%:Z - k%:Z * 2, 1 ])
    \/
    (exists k : nat, (k <= n - m - 1)%N /\
     \big[matmult / I]_(m <= i < n) Sn d f g (n + m - i.+1) =
     [ 1, 0; n%:Z - m%:Z - k%:Z * 2, -1 ]).
Proof.
  case: n => [ // | n ]. elim: n => [ | n IH ].
  - rewrite ltnS leqn0 => /eqP ->. rewrite subn0 subnn.
    rewrite big_nat1 subnn /Sn /Smat /divstepn /=.
    case: ((0 < d) && oddz g).
    + right. exists 0%N. by split.
    + left. exists 0%N. by split.
  - rewrite ltnS leq_eqVlt. case/orP => [ /eqP -> | mltSn ].
    + rewrite -addn1 subnAC -addnBA // subnn addn0 subSS subnn.
      rewrite addn1 big_nat1 -addnBAC //. rewrite subnn add0n.
      rewrite /Sn /Smat.
      case: ((0 < (divstepn d f g n.+1).1.1) && oddz (divstepn d f g n.+1).2).      
      * right. exists 0%N. split. by [].
        entrywise. intring.
      * left. exists 0%N. split. by [].
        entrywise. intring. 
  - rewrite big_nat_recl; last (rewrite ltnW //; exact mltSn).
    have: forall i, (m <= i < n.+1)%N -> (Sn d f g (n.+2 + m - i.+2) = Sn d f g (n.+1 + m - i.+1)).
    move=> i H. by rewrite addnC -addn1 addnA  -[ i.+2 ](addn1) subnDA subnAC -addnBA // subnn addn0 addnC.
    move=> H. rewrite (eq_big_nat I matmult H){H}.
    move: (IH mltSn).
    have: (n.+2 + m - m.+1 = n.+1)%N.
    by rewrite -addn1 -addnA [ (1 + m)%N ]addnC addn1 -addnBA // subnn addn0. move=> ->.
    case => {IH} [ [k] | [k] ] [kbound] ->.
    + rewrite /Sn /Smat.
      case: ((0 < (divstepn d f g n.+1).1.1) && oddz (divstepn d f g n.+1).2).
      * rewrite /matmult /=. right. exists (n.+1 - m - k)%N. split.
        ** by rewrite [(_ - _ - 1)%N]subnAC subSS subn0 leq_subr.
        ** entrywise. intring.
           rewrite -subzn; [ |apply (leq_trans kbound); rewrite subn1; apply leq_pred].
           rewrite -subzn; last (rewrite ltnW //; exact mltSn).
           intring.
      * rewrite /matmult /=. left. exists k. split.
        ** apply (leq_trans kbound). by rewrite [(n.+2 - _ - 1)%N]subnAC subSS subn0 leq_subr.
        ** entrywise; intring.
    + rewrite /Sn /Smat /matmult.
      case: ((0 < (divstepn d f g n.+1).1.1) && oddz (divstepn d f g n.+1).2) => /=.
      * left. exists (n.+1 - m - k)%N. split.
        ** by rewrite [(_ - _ - 1)%N]subnAC subSS subn0 leq_subr.
        ** entrywise. intring.
           rewrite -subzn; [ |apply (leq_trans kbound); rewrite subn1; apply leq_pred].
           rewrite -subzn; last (rewrite ltnW //; exact mltSn).
           intring.
      * right. exists k. split.
        ** apply (leq_trans kbound). by rewrite [(n.+2 - _ - 1)%N]subnAC subSS subn0 leq_subr.
        ** entrywise; intring. Qed.


Lemma oddz_modz f : oddz f = (f %% 2 == 1).
Proof.
  case H: (oddz f).
  rewrite oddzmod2 //. 
  rewrite noddzmod2 //. by rewrite H. Qed.
  
Lemma noddz_modz f : ~~ oddz f = (f %% 2 == 0).
Proof.
  case H: (~~ (oddz f)).
  rewrite noddzmod2. by []. by []. 
  rewrite oddzmod2. by []. by rewrite -(negbK (oddz f)) H. Qed.
  
Lemma congW m x y d : d %| m -> x %% m = y %% m -> x %% d = y %% d. 
Proof.
  move=> /dvdzP [q1] -> /eqP. rewrite eqz_mod_dvd => /dvdzP [q2] xminy. apply /eqP. rewrite eqz_mod_dvd.
  apply /dvdzP. exists (q2 * q1). rewrite xminy. intring. Qed.

Lemma mulz_inj x : x != 0 -> injective (mulz x).
Proof.
  apply mulfI. Qed.

(*
Lemma modz_divz (a b d m : int) : 0 <= d -> d %| a -> d %| b -> a = b %[mod m] -> (a %/ d)%Z = (b %/ d)%Z %[mod m].
Proof.
  rewrite ler_eqVlt => /orP [/eqP /esym ->|].
  - by rewrite !dvd0z => /eqP -> /eqP ->.
  - move=> dgt0 ddiva ddivb aeqbmodm. rewrite /modz. rewrite -!divzMA_ge0.
    move: (lt0r d) dgt0 -> => /andP [] /mulfI inj dge0. apply inj.
    rewrite mulrC [in RHS]mulrC !mulrDl. rewrite !divzK //.
    rewrite !mulNr -!mulrA [m * d]mulrC. 
    *)

Require Import Psatz.

Lemma mulcBl A v w : A *col v - A *col w = A *col (v - w).
Proof.
  case: A => a b c d; case v => v1 v2; case w => w1 w2.
  rewrite /colmult /=; entrywise_col; intring. Qed.       

Theorem _9_4 (d f g d' f' g' : int) (n m t : nat) :
  (m < n <= m + t)%N 
  -> (oddz f)
  -> (oddz f')
  -> dn d f g m = dn d' f' g' m
  -> (fn d f g m = fn d' f' g' m %[mod (2%:Z ^+ t)%N])
  -> (gn d f g m = gn d' f' g' m %[mod (2%:Z ^+ t)%N])
  ->
  (Tn d f g (n - 1) = Tn d' f' g' (n - 1)) /\
  (Sn d f g (n - 1) = Sn d' f' g' (n - 1)) /\
  dn d f g n = dn d' f' g' n /\
  (fn d f g n = fn d' f' g' n %[mod (2%:Z ^+ (t - (n - m - 1)))%N]) /\
  (gn d f g n = gn d' f' g' n %[mod (2%:Z ^+ (t - (n - m)))%N]).
Proof.
  case: t => [|t]. rewrite addn0 => /andP [c1 c2].
  have: (n < n)%N. by apply (leq_ltn_trans c2 c1). by rewrite ltnn.
  
  elim/(@strong_induction_from_m (m.+1)): n => [n||n].
  - rewrite ltnS. move=> nltm => /andP [] mltn. move: (leq_ltn_trans nltm mltn). by rewrite ltnn.
  - move=> /andP []. 
    rewrite subn1 -pred_Sn subSnn subnn subn0 subn1 -pred_Sn.
    move=> H{H} H{H} fodd f'odd dmdm' fmfm' gmgm'.
    
    have: (gn d f g m %% 2)%Z = (gn d' f' g' m %% 2)%Z.
    apply congW with (2%:Z ^+ t.+1). rewrite exprS. apply /dvdzP. rewrite mulrC. by eexists. exact gmgm'.
    move=> gmgm'mod2.
    
    have: oddz (gn d f g m) = oddz (gn d' f' g' m).
    rewrite !oddz_modz. by rewrite gmgm'mod2.
    move=> gmgm'oddz.

    have: (fn d f g m %% 2)%Z = (fn d' f' g' m %% 2)%Z.
    apply congW with (2%:Z ^+ t.+1). rewrite exprS. apply /dvdzP. rewrite mulrC. by eexists. exact fmfm'.
    move=> fmfm'mod2.
    
    have: oddz (fn d f g m) = oddz (fn d' f' g' m).
    rewrite !oddz_modz. by rewrite fmfm'mod2.
    move=> fmfm'oddz.

    have: oddz (fn d' f' g' m).
    rewrite -fmfm'oddz. by apply fodd_fnodd. 
    move=> f'modd.
    
    split; last split; last split; last split.
    + rewrite /Tn /Tmat. folddefs.
      by rewrite gmgm'oddz dmdm' gmgm'mod2.
    + rewrite /Sn /Smat; folddefs.
      by rewrite gmgm'oddz dmdm'.
    + rewrite /dn /divstepn /divstep; folddefs. rewrite dmdm' gmgm'oddz.
      by case ((0 < dn d' f' g' m) && oddz (gn d' f' g' m)).
    + rewrite /fn /divstepn /divstep; folddefs. rewrite dmdm' gmgm'oddz.
      by case: ((0 < dn d' f' g' m) && oddz (gn d' f' g' m)).
    + rewrite /gn /divstepn /divstep; folddefs. rewrite dmdm' gmgm'oddz.
      case H: ((0 < dn d' f' g' m) && oddz (gn d' f' g' m)) => /=.
      * have: 2%:Z != 0 by [] => H1; apply: (mulfI H1) => {H1}. rewrite mulrC [in RHS]mulrC.
        rewrite !mulz_modl //. rewrite -exprSr !divzK. rewrite -modzDm. rewrite gmgm'.
        have: - (fn d f g m) = - (fn d' f' g' m) %[mod 2%:Z ^+ t.+1]. apply /eqP.
        rewrite eqz_mod_dvd. rewrite opprK addrC -opprB -mulN1r. apply (dvdz_mull).
        move: fmfm' => /eqP. by rewrite eqz_mod_dvd. move=> Nfmfm'.
        rewrite Nfmfm'. by rewrite modzDm.
        apply /noddzdvdzP. rewrite oddz_add.
        move: H => /andP [] H2 ->. rewrite -oddz_opp. by rewrite f'modd.
        apply /noddzdvdzP. rewrite oddz_add gmgm'oddz.
        move: H => /andP [] H2 ->. rewrite -oddz_opp. by rewrite fodd_fnodd.
      * have: 2%:Z != 0 by [] => H1; apply: (mulfI H1) => {H1}. rewrite mulrC [in RHS]mulrC.
        rewrite [_ * 2%:Z]mulz_modl //.
        rewrite [_ * 2%:Z in RHS]mulz_modl //. rewrite -exprSr !divzK. rewrite -modzDm.
        rewrite gmgm' gmgm'mod2.
        case H1: (oddz (gn d' f' g' m)).
        ** rewrite oddzmod2 //. 
           by rewrite !mul1r fmfm' modzDm.
        ** rewrite noddzmod2.
           by rewrite !mul0r mod0z !addr0 modz_mod. by rewrite H1.
        case: (oddz (gn d' f' g' m))/idP => [H1 | /negP H1].
        ** apply /noddzdvdzP. rewrite oddz_add oddz_mul H1 oddzmod2 //. by rewrite f'modd. 
        ** apply /noddzdvdzP. rewrite oddz_add oddz_mul negb_add. apply /eqP. apply negb_inj.
           rewrite H1 noddzmod2 //.
        case: (oddz (gn d f g m))/idP => [H1 | /negP H1].
        ** apply /noddzdvdzP. rewrite oddz_add oddz_mul H1 oddzmod2 //. by rewrite fodd_fnodd. 
        ** apply /noddzdvdzP. rewrite oddz_add oddz_mul negb_add. apply /eqP. apply negb_inj.
           rewrite H1 noddzmod2 //.
  - case: n => [// |n ]. rewrite ltnS => mltn IH.

    move=> /andP [] H{H} => nltmSt fodd f'odd dmdm' fmfm' gmgm'.
    have: (0 <= m)%N by [] => /leq_ltn_trans /(_ mltn) ngt0.

    have: (m < n <= m + t.+1)%N. apply /andP. split. exact mltn. apply ltnW. exact nltmSt.
    move=> mltnltmlemSt.
    
    have: (m < m + t.+1)%N. by rewrite addnS -addSn leq_addr. move=> H.
    move: (@ltn_sub2r m n (m + t.+1) H nltmSt) => {H}. rewrite addnC -addnBA // subnn addn0 ltnS => nsubmlet. 

    rewrite subSn //. rewrite subnSK //. rewrite subn0.

    move: (IH n (ltnSn n) mltnltmlemSt fodd f'odd dmdm' fmfm' gmgm'). 
    rewrite subSn; [ | rewrite -[t]subn0; apply leq_sub; by []].
    rewrite [(t.+1 - _)%N]subSn //.

    move=> [IHTnTn' [IHSnSn' [IHdndn' [IHfnfn' [IHgngn']]]]].

    have: (gn d f g n %% 2)%Z = (gn d' f' g' n %% 2)%Z.
    apply (@congW (2%:Z ^+ (t - (n - m)).+1)). 
    rewrite exprS. apply /dvdzP. rewrite mulrC. by eexists. exact IHgngn'.
    move=> gngn'mod2.
    
    have: oddz (gn d f g n) = oddz (gn d' f' g' n).
    rewrite !oddz_modz. by rewrite gngn'mod2.
    move=> gngn'oddz.

    have: (fn d f g n %% 2)%Z = (fn d' f' g' n %% 2)%Z.
    apply (@congW (2%:Z ^+ (t - (n - m - 1)).+1)).
    rewrite exprS. apply /dvdzP. rewrite mulrC. by eexists. exact IHfnfn'.
    move=> fnfn'mod2.
    
    have: oddz (fn d f g n) = oddz (fn d' f' g' n).
    rewrite !oddz_modz. by rewrite fnfn'mod2.
    move=> fnfn'oddz.

    have: oddz (fn d' f' g' n).
    rewrite -fnfn'oddz. by apply fodd_fnodd.
    move=> f'nodd.

    have: Sn d f g n = Sn d' f' g' n.
    rewrite /Sn /Smat; folddefs. by rewrite IHdndn' gngn'oddz. move=> SnSn'.

    have: Tn d f g n = Tn d' f' g' n.
    rewrite /Tn /Tmat. folddefs. by rewrite IHdndn' gngn'oddz gngn'mod2. move=> TnTn'.

    have: exists x y v w,
        ([fn d' f' g' n.+1; gn d' f' g' n.+1] - [fn d f g n.+1; gn d f g n.+1]) *
        [2%:Z ^+ (n.+1 - m); 2%:Z ^+ (n.+1 - m)] =
        [x * 2%:Z, y * 2%:Z; v, w] *col ([fn d' f' g' m; gn d' f' g' m] - [fn d f g m; gn d f g m]).
    have: \big[ matmult / I ]_( m <= i < n.+1 ) Tn d f g (n.+1 + m - i.+1 ) =
            \big[ matmult / I ]_( m <= i < n.+1 ) Tn d' f' g' (n.+1 + m - i.+1 ).
      apply eq_big_nat => i /andP []. rewrite leq_eqVlt => /orP [/eqP /esym -> H{H}|].
      * rewrite subnS -addnBA // subnn addn0. by rewrite -pred_Sn.
      * move=> mlti iltSn.

        have: ((n + m - i).+1 < n.+1)%N.
        rewrite -subSn. rewrite -(ltn_add2r i) -[(n + m)%N]addnC. rewrite addnBAC. rewrite -subnBA // subnn subn0.
        rewrite [(n.+1 + i)%N]addnC. rewrite addnS ltnS. by rewrite ltn_add2r.
        rewrite addnC. rewrite -addnS.
        move: iltSn. rewrite ltnS. move=> ilen. apply (leq_trans ilen (leq_addr m.+1 n)).
        move: iltSn. rewrite ltnS. move=> ilen. apply (leq_trans ilen (leq_addr m n)).
        move=> i'ltSn.

        have: (m < (n + m - i).+1 <= m + t.+1)%N.
        apply /andP. split.
        ** rewrite addnC -addnBA // ltnS. apply leq_addr. 
        ** move: mltnltmlemSt i'ltSn => /andP [] H{H} nlemSt. rewrite ltnS => i'ltSn.
           apply (leq_trans i'ltSn nlemSt).

        move=> H.
           
        move: (IH (n + m - i).+1%N i'ltSn H fodd f'odd dmdm' fmfm' gmgm'). rewrite subn1 -pred_Sn. move=> [].
        move=> H1 H2{H2}. by rewrite -addn1 -addnA [(1 + m)%N]addnC addnA addn1 subSS. 

      move=> mat_equality. 
      pose P := \big[matmult/I]_(m <= i < n.+1) Tn d f g (n.+1 + m - i.+1).

      move: (@_9_1_1 d' f' g' (n.+1) m (leqW (ltnW mltn)) f'odd).
      move=> /(f_equal (fun v => v - ([ fn d f g n.+1 ; gn d f g n.+1 ] ** 2%:Z ^+ (n.+1 - m)))).

      rewrite -mat_equality.
      rewrite [in RHS](@_9_1_1 d f g (n.+1) m (leqW (ltnW mltn)) fodd).
      rewrite /colscale. rewrite -mulrBl. rewrite mulcBl.
      move: (@_9_2 d f g n.+1 m fodd (ltnW mltn)) => [x [y [v [w]]]] ->.
      by exists x; exists y; exists v; exists w. move=> lemma.
    
    split; last split; last split; last split.
    + exact TnTn'.
    + exact SnSn'.
    + have: ([1 ; (dn d f g n)] = [1 ; (dn d' f' g' n)]) by rewrite IHdndn'.
      move=> /(f_equal (colmult (Sn d f g n))).
      rewrite -Sn_transition. rewrite SnSn'. rewrite -Sn_transition. by case.
    + move: lemma => [x [y [v [w]]]] [] H H1{H1}. move: H.
      move: fmfm' => /esym /eqP. rewrite eqz_mod_dvd => /dvdzP [q] ->.
      move: gmgm' => /esym /eqP. rewrite eqz_mod_dvd => /dvdzP [p] ->.
      rewrite -!mulrA ![2%:Z * _]mulrC -!mulrA -exprSr. rewrite mulrA [y * _]mulrA.
      rewrite -mulrDl. 
      have: t.+2 = (t.+1 - (n.+1 - m - 1) + (n.+1 - m))%N.
      rewrite subnBA. rewrite addnBAC.
      by rewrite -[((t.+1 + 1) + (n.+1 - m) - (n.+1 - m))%N]addnBA // subnn addn0 addn1.
      rewrite subSn; last exact (ltnW mltn). rewrite addn1. rewrite ltnS.
      by eapply (@leq_trans t).
      rewrite subSn //. exact (ltnW mltn). move=> ->.
      rewrite [in RHS]exprD. have: 2%:Z ^+ (n.+1 - m) != 0. by apply expf_neq0. move=> neq0.
      rewrite mulrA. move=> /(mulIf neq0). move=> fSnsubf'Sn. apply /esym /eqP. rewrite eqz_mod_dvd.
      apply /dvdzP. eexists. by rewrite fSnsubf'Sn.
    + move: lemma => [x [y [v [w]]]] [] H{H}.
      move: fmfm' => /esym /eqP. rewrite eqz_mod_dvd => /dvdzP [q] ->.
      move: gmgm' => /esym /eqP. rewrite eqz_mod_dvd => /dvdzP [p] ->.
      rewrite !mulrA. rewrite -mulrDl. 
      have: t.+1 = (t.+1 - (n.+1 - m) + (n.+1 - m))%N.
      rewrite addnBAC.
      by rewrite -[(t.+1 + (n.+1 - m) - (n.+1 - m))%N]addnBA // subnn addn0.
      rewrite subSn; last exact (ltnW mltn). rewrite ltnS. exact nsubmlet. move=> {1}->.
      rewrite [in RHS]exprD. have: 2%:Z ^+ (n.+1 - m) != 0. by apply expf_neq0. move=> neq0.
      rewrite mulrA. move=> /(mulIf neq0). move=> gSnsubg'Sn. apply /esym /eqP. rewrite eqz_mod_dvd.
      apply /dvdzP. eexists. by rewrite gSnsubg'Sn.
Qed.

End _9.

Section _11.

Definition un f g n :=
  a11 (\big[ matmult / I ]_( 0 <= i < n ) Tn 1 f g (n - i.+1)).
Definition vn f g n :=
  a12 (\big[ matmult / I ]_( 0 <= i < n ) Tn 1 f g (n - i.+1)).
Definition qn f g n :=
  a21 (\big[ matmult / I ]_( 0 <= i < n ) Tn 1 f g (n - i.+1)).
Definition rn f g n :=
  a22 (\big[ matmult / I ]_( 0 <= i < n ) Tn 1 f g (n - i.+1)).

From mathcomp Require Import all_field. 

End _11.
  
End withOwnMatMult.

Search "modulo".
Search "mod".

Import Lia.

Lemma modmod (n p : nat) (Hp : (0 < p)%nat) : (n %% p)%nat = Nat.modulo n p.
Proof.
  unfold Nat.modulo.
  destruct p. easy. simpl.  
  destruct (Nat.divmod n p 0 p) eqn:E.
  assert (p <= p)%coq_nat. lia.
  apply (PeanoNat.Nat.divmod_spec n _ 0) in H. rewrite E in H.
  destruct H.  simpl.

  rewrite <- mult_n_O in H. 
  rewrite PeanoNat.Nat.sub_diag in H.
  rewrite <- !plus_n_O in H. rewrite H.
  rewrite <- modnDml.
  assert ((p.+1 * n0)%coq_nat %% p.+1 = 0)%nat.
  rewrite multE.
  rewrite modnMr. reflexivity. rewrite H1.
  rewrite add0n. rewrite minusE. rewrite modn_small. reflexivity.
  rewrite sub_ord_proof. easy. Qed.
