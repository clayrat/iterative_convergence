(** Here we are attempting to prove that
if the magnitude of all the eigen values
of a matrix is less than 1, then
\lim_{m \to \infty} ||S^m|| = 0, where
||.|| is a matrix norm **)

Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp Require Import mxalgebra matrix mxpoly all_field.
From mathcomp.analysis Require Import boolp Rstruct classical_sets signed topology normedtype sequences.
From CoqEAL Require Import mxstructure jordan similar closed_poly frobenius_form.
From Coquelicot Require Import Lim_seq Rbar Hierarchy Lub.
Require Import complex_mat_vec_prop matrix_norm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.
Open Scope classical_set_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

From mathcomp.real_closed Require Import complex.
Import ComplexField.

Lemma V_exists:
forall (n:nat) (A: 'M[complex R]_n.+1),
  exists2 V, V \in unitmx &
      mulmx V A = mulmx (conform_mx V (Jordan_form A)) V.
Proof.
by apply Jordan.
Qed.



(** If A= B , C*A = C*B **)
Lemma matrix_eq1:
  forall (n m p:nat) (A B C: 'M[complex R]_n.+1),
   A = B -> mulmx C A = mulmx C B.
Proof.
intros. rewrite H. reflexivity.
Qed.


Lemma big_sum_ge_ex_abstract I r (P: pred I) (E1 E2: I -> R):
  (forall i, P i -> (E1 i <= E2 i)%Re) ->
  (\big[+%R/0]_(i <-r | P i) E1 i <= \big[+%R/0]_(i <-r | P i) E2 i).
Proof.
move => leE12. apply /RleP. apply big_ind2.
+ nra.
+ intros. rewrite -!RplusE. by apply Rplus_le_compat.
+ apply leE12.
Qed.


Lemma big_split_sum_prod (n:nat) F1 F2:
  (forall i:'I_n.+1, (0<=F1 i)%Re /\ (0<=F2 i)%Re) ->
  \big[+%R/0]_(i < n.+1) (F1 i * F2 i)%Re <=
    \big[+%R/0]_(i < n.+1) F1 i * \big[+%R/0]_(i < n.+1) F2 i.
Proof.
induction n.
+ rewrite !big_ord_recr  !big_ord0//= !add0r.
  by rewrite RmultE.
+ intros. rewrite big_ord_recr //=.
  assert (\big[+%R/0]_(i < n.+2) F2 i =
          (\big[+%R/0]_(i < n.+1) F2
                          (widen_ord (leqnSn n.+1) i) + F2 ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H0. clear H0.
  assert (\big[+%R/0]_(i < n.+2) F1 i =
          (\big[+%R/0]_(i < n.+1) F1
                          (widen_ord (leqnSn n.+1) i) + F1 ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H0. clear H0. apply /RleP.
  apply Rle_trans with
  ((\big[+%R/0]_(i < n.+1) F1
                          (widen_ord (leqnSn n.+1) i) *
    \big[+%R/0]_(i < n.+1) F2
                          (widen_ord (leqnSn n.+1) i)) +
   (F1 ord_max * F2 ord_max)%Re).
  - apply Rplus_le_compat_r.
    rewrite -RmultE. apply /RleP. apply IHn.
    intros. specialize (H (widen_ord (leqnSn n.+1) i)).
    apply H.
  - rewrite -!RplusE. rewrite !RmultE. rewrite -!RmultE.
    assert (forall a b c d:R,
            (0<=a)%Re -> (0<=b)%Re -> (0<=c)%Re -> (0<=d)%Re ->
          ((a *b + c * d) <= ((a+c) * (b+d)))%Re).
    { intros. nra. } apply H0.
    * rewrite -(big_0_sum n).
      apply /RleP. apply big_sum_ge_ex_abstract. intros.
      specialize (H (widen_ord (leqnSn n.+1) i)). by destruct H.
    * rewrite -(big_0_sum n).
      apply /RleP. apply big_sum_ge_ex_abstract. intros.
      specialize (H (widen_ord (leqnSn n.+1) i)). by destruct H.
    * specialize (H ord_max). by destruct H.
    * specialize (H ord_max). by destruct H.
Qed.




(** the frobenius matrix norm is greater than 0 **)
Lemma mat_norm_ge_zero:
  forall (n:nat) (A B: 'M[complex R]_n.+1),
  (0 <= mat_norm A)%Re.
Proof.
intros. unfold mat_norm. apply sqrt_pos.
Qed.

(** If matrices A and B are equal, their norms are equal as well **)
Lemma mat_norm_eq: forall (n:nat) (A B: 'M[complex R]_n.+1),
   A = B -> mat_norm A = mat_norm B.
Proof.
intros. by rewrite H.
Qed.

(** Properties of conform_mx between two matrices **)
Lemma matrix_norm_equality:
  forall (m n:nat) (A : 'M[complex R]_m.+1) (B: 'M[complex R]_n.+1),
  m = n ->
  mat_norm (conform_mx B A) = mat_norm A.
Proof.
by move=> m n A B mn; move: B; rewrite -mn => B; rewrite conform_mx_id.
Qed.

Lemma conform_mx_mult: forall (m n:nat) (A : 'M[complex R]_m.+1)
 (B C: 'M[complex R]_n.+1), m = n ->
  conform_mx A (B * C) = (conform_mx A B) *(conform_mx A C).
Proof.
by move=> m n A B C mn; move: B C; rewrite -mn=> B C; rewrite !conform_mx_id.
Qed.

Lemma conform_mx_mat_power:
  forall (m n k:nat) (A : 'M[complex R]_m.+1) (B: 'M[complex R]_n.+1),
  m=n ->
  (conform_mx B A)^+k.+1 = conform_mx B (A^+k.+1).
Proof.
by intros m n k A B mn; move: B; rewrite -mn=> B; rewrite !conform_mx_id. Qed.



Lemma eigen_matrix_set (n:nat) (A: 'M[complex R]_n.+1):
  { V : 'M_n.+1 | ((V \in unitmx) &&
    (V *m A == conform_mx V (Jordan_form A) *m V ))}.
Proof.
apply: sigW.
case: (V_exists A)=> P Pu PA.
exists P; apply/andP; split;[exact: Pu | apply/eqP; exact PA].
Qed.


Lemma total_eigen_val: forall (n:nat) (A: 'M[complex R]_n.+1),
 (size_sum
  [seq x.2.-1 | x <- root_seq_poly (invariant_factors A)]).+1 = n.+1.
Proof.
by move=> n A; rewrite -(proj1 (Jordan A)).
Qed.


Lemma invert_vec_not_zero (n:nat) (A: 'M[complex R]_n.+1):
  A \in unitmx ->
  (exists v : 'rV_n.+1, v <= A /\ v != 0)%MS .
Proof.
intros. apply mxrank_unit in H.
assert (\rank A != 0%N). { by rewrite H. }
rewrite mxrank_eq0 in H0.
assert ((exists2 v : 'rV_n.+1, v <= A & v != 0)%MS).
{ by apply /rowV0Pn. } destruct H1 as [v H1].
exists v. by split.
Qed.

Definition lambda_seq (n: nat) (A: 'M[complex R]_n.+1):=
  let sizes:= size_sum
        [seq x.2.-1
           | x <- root_seq_poly (invariant_factors A)] in
   [seq (Jordan_form A) i i | i <- enum 'I_sizes.+1].



Lemma Jordan_ii_is_eigen_aux:
 forall (n: nat) (A: 'M[complex R]_n.+1),
  let sizes:= size_sum
        [seq x.2.-1
           | x <- root_seq_poly (invariant_factors A)] in
  forall  (i: 'I_sizes.+1),
    @eigenvalue (complex_fieldType _) n.+1 A (@nth _  0%C (lambda_seq A) i).
Proof.
intros.
rewrite eigenvalue_root_char.
rewrite -root_root_seq.
+ assert (perm_eq [seq (Jordan_form A) i i | i <- enum 'I_(sizes).+1]
          (root_seq (char_poly A))).
  { apply eigen_diag. }
  apply perm_mem in H. unfold eq_mem in H.
  specialize (H (@nth _  0%C (lambda_seq A) i)).
  rewrite -H. rewrite /lambda_seq. apply mem_nth.
  by rewrite size_map size_enum_ord.
+ apply monic_neq0. apply char_poly_monic.
Qed.


Lemma Jordan_ii_is_eigen:
 forall (n: nat) (A: 'M[complex R]_n.+1),
  forall  (i: 'I_n.+1),
    @eigenvalue (complex_fieldType _) n.+1 A (@nth _  0%C (lambda_seq A) i).
Proof.
intros.
assert (forall (n: nat) (A: 'M[complex R]_n.+1),
        let sizes:= size_sum
              [seq x.2.-1
                 | x <- root_seq_poly (invariant_factors A)] in
        forall  (i: 'I_sizes.+1),
          @eigenvalue (complex_fieldType _) n.+1 A (@nth _  0%C (lambda_seq A) i)).
{ apply Jordan_ii_is_eigen_aux. }
specialize (H n A). simpl in H.
rewrite total_eigen_val in H.
apply H.
Qed.

(** Define i^th eigen value **)
Definition lambda (n: nat) (A: 'M[complex R]_n.+1) (i: 'I_n.+1) :=
  (@nth _  0%C (lambda_seq A) i).


(** Here we use the expansion of the Jordan block J^m **)
Lemma diag_ext: forall (n n0:nat) (A: 'M[complex R]_n.+1),
diag_block_mx
  [seq x0.2.-1
     | x0 <- root_seq_poly (invariant_factors A)]
  (fun n1 i0 : nat =>
   \matrix_(i1, j) ('C(n0.+1, j - i1)%:R*
                    (nth (0, 0%N)
                       (root_seq_poly
                          (invariant_factors A)) i0).1
                    ^+ (n0.+1 - (j - i1)) *+
                    (i1 <= j))) =
diag_block_mx
  [seq x0.2.-1
     | x0 <- root_seq_poly (invariant_factors A)]
  (fun n1 i0 : nat =>
   @Jordan_block [ringType of (complex R)]
     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
        i0).1 n1.+1 ^+ n0.+1).
Proof.
intros. apply ext_block.
intros. by rewrite Jordan_expn.
Qed.


Lemma lim_exp_0 (x : [archiFieldType of R]) : `|x| < 1 ->
  ((fun n => x ^+ n) --> 0%Re).
Proof.
move=> modxlt1.
have := cvg_geometric 1 modxlt1.
suff -> : geometric 1 x = [eta GRing.exp x] by [].
apply: funext => n.
by rewrite /geometric /= mul1r.
Qed.



Lemma diag_destruct (R: ringType)
  (s : seq nat) (F : (forall n, nat -> 'M[R]_n.+1)):
  forall i j: 'I_(size_sum s).+1,
  (exists k l m n,
    (k <= size_sum s)%N /\ (l <= size_sum s)%N /\
    (forall p:nat, (diag_block_mx s (fun k l:nat => (F k l)^+ p.+1)) i j =
                  ((F k l)^+ p.+1) m n) /\
    (diag_block_mx s F i i = (F k l) m m)) \/
    (forall p:nat, (diag_block_mx s (fun k l:nat => (F k l)^+ p.+1)) i j = 0).
Proof.
case: s => [ | s0 s].
+ simpl. intros. right. intros.
  by rewrite mxE.
+ rewrite /diag_block_mx.
  elim: s s0 F=> [ | s1 s Ih] s0 F /= i j.
  * left. by exists s0, 0%N, i,j.
  * have shifts (x : 'I_(s0 + (size_sum_rec s1 s).+1).+1) :
   (forall (xles0 : (x < s0.+1)%N), x = lshift _ (Ordinal xles0)) *
   (forall (xgts0 : (s0 < x)%N), x = rshift s0.+1
             (inord (x - s0.+1) : 'I_(size_sum_rec s1 s).+1)).
  split;[by move=> xles0; apply/val_inj | ].
  move=> xgts0; have xltsum : (x - s0.+1 < (size_sum_rec s1 s).+1)%N.
    by rewrite ltn_subLR //; case: (x).
  by apply/val_inj; rewrite /= inordK // subnKC.
case : (ltnP i s0.+1)=> [ilts0 | iges0];
  case : (ltnP j s0.+1)=> [jlts0 | jges0].
- left; exists s0, 0%N, (Ordinal ilts0), (Ordinal jlts0)=> /=.
  split.
  * by apply leq_addr.
  * split.
    ++ by [].
    ++ split.
       -- intros. rewrite [in LHS]((shifts _).1 ilts0) [in LHS]((shifts _).1 jlts0).
          by rewrite [LHS]block_mxEul.
       -- rewrite [in LHS]((shifts _).1 ilts0). by rewrite [LHS]block_mxEul.
- right.  intros.
    rewrite [in LHS]((shifts _).1 ilts0) [in LHS]((shifts _).2 jges0).
    by rewrite [LHS]block_mxEur mxE.
- right. intros.
  rewrite [in LHS]((shifts _).2 iges0) [in LHS]((shifts _).1 jlts0).
  by rewrite [LHS]block_mxEdl mxE.
have := ((shifts _).2 iges0); have := ((shifts _).2 jges0).
set i' := inord (i - s0.+1); set j' := inord (j - s0.+1)=> jq iq.
have := (Ih s1 (fun m i => F m i.+1) i' j').
case => [[k [l [m [n Main]]]] | Main]; last first.
  by right; intros; rewrite iq jq [LHS]block_mxEdr.
left; exists k, l.+1, m, n. destruct Main as [Main' Main].
destruct Main as [Main'' Main].
split.
+ rewrite /size_sum in Main'.
  apply leq_trans with (s0 + size_sum_rec s1 s)%N.
  - assert (k = (0 + k)%N). { by []. } rewrite H.
    apply leq_add.
    * by [].
    * by apply Main'.
  - by apply leq_add.
+ split.
  - rewrite /size_sum in Main''.
    apply leq_ltn_trans with (s0 + size_sum_rec s1 s)%N.
    * assert (l = (0 + l)%N). { by []. } rewrite H.
        apply leq_add.
        ++ by [].
        ++ by apply Main''.
    * by rewrite ltn_add2l.
  - intros. split.
    * intros. rewrite iq jq [LHS]block_mxEdr. apply Main.
    * rewrite iq [LHS]block_mxEdr. apply Main.
Qed.



(** Compatibility of the multiplication of naturals
  and their cast to complex ring type **)
Lemma mul_ring: forall (m n:nat),
    (m * n)%:R = (m%:R * n %:R) :> complex R.
Proof.
intros. induction n.
+ by rewrite mulr0 muln0.
+ rewrite mulnS mulrS mulrDr mulr1.
  by rewrite -IHn natrD.
Qed.

(** Compatibility of the multiplication of naturals
  and their cast to real ring type **)
Lemma mul_ring_real: forall (m n:nat),
  (m * n)%:R = m%:R * n%:R :>R.
Proof.
intros. induction n.
+ by rewrite mulr0 muln0.
+ rewrite mulnS mulrS mulrDr mulr1.
  by rewrite -IHn natrD.
Qed.

(** Proof that factorial(n) <= n^n **)
Lemma n_fact_le_pow: forall (n:nat),
  (n`! <= n^n)%N.
Proof.
intros. induction n.
+ by rewrite expn0 fact0.
+ rewrite factS expnS. apply leq_mul.
  - by [].
  - apply leq_trans with (n^n)%N.
    * apply IHn.
    * assert ( (0%N==n) \/ (0<n)%N).
      { apply /orP. by rewrite -leq_eqVlt. }
      destruct H.
      { assert ( n= 0%N). { apply /eqP. by rewrite eq_sym. }
        rewrite H0. by rewrite !expn0.
      }
      { rewrite leq_exp2r; by []. }
Qed.

Lemma fact_pow_rel: forall (n k:nat),
  (n^_k <= n^k)%N.
Proof.
induction k.
+ by rewrite expn0 ffactn0.
+ rewrite ffactnSr expnS mulnC.
  apply leq_mul.
  + apply leq_subr.
  + apply IHk.
Qed.


Lemma n_plus_1_not_0: forall (n:nat),
  (0 < (n.+1)%:R)%Re.
Proof.
intros. induction n.
+ apply Rlt_0_1.
+ rewrite -addn1 natrD. apply Rplus_lt_0_compat.
  - apply IHn.
  - apply Rlt_0_1.
Qed.


Lemma fact_ring_gt_0: forall (n:nat),
  (0 < n`!%:R)%Re.
Proof.
intros. induction n.
+ rewrite fact0. apply Rlt_0_1.
+ rewrite factS. rewrite mul_ring_real.
  apply Rmult_lt_0_compat.
  - apply n_plus_1_not_0.
  - apply IHn.
Qed.

Lemma leq_not_0: forall (x: complex R),
  (0 < x)%C -> x != 0.
Proof.
intros. destruct x. rewrite ltcE in H.
simpl in H. rewrite eq_complex //=.
apply /nandP. left.
assert ( (Im == 0) /\ (0 < Re)). { by apply /andP. }
destruct H0. apply /eqP.
assert ( (0 < Re)%Re -> Re <> 0%Re). { nra. }
apply H2. by apply /RltP.
Qed.

(** Imaginary part of the coercion from nat to complex = 0 **)
Lemma nat_complex_0: forall (k:nat),
  Im (k%:R) = 0%Re.
Proof.
intros. induction k.
+ by rewrite //=.
+ rewrite -addn1 natrD Im_add IHk add0r //=.
Qed.

(** Real part of the coercion from nat to complex > 0 **)
Lemma Re_complex_gt_0: forall (k:nat),
  (0 < Re k.+1%:R)%Re.
Proof.
intros. induction k.
+ rewrite //=. apply Rlt_0_1.
+ rewrite -addn1 natrD Re_add.
  apply Rplus_lt_0_compat.
  - apply IHk.
  - rewrite //=. apply Rlt_0_1.
Qed.

Lemma fact_complex_ring_not_0: forall (k:nat),
  k`!%:R != 0 :> complex R.
Proof.
intros. apply leq_not_0. induction k.
+ by rewrite fact0.
+ rewrite factS mul_ring. rewrite ltcE //=.
  rewrite ltcE in IHk. simpl in IHk.
  assert ((Im k`!%:R == 0%Re) /\ (0%Re < Re k`!%:R)).
  { by apply /andP. } apply /andP.
  split.
  - destruct H. apply /eqP.
    assert ( Im k`!%:R = 0%Re). { by apply /eqP. }
    rewrite Im_complex_prod H1 mulr0 add0r.
    by rewrite nat_complex_0 mul0r.
  - rewrite Re_complex_prod. destruct H.
    assert ( Im k`!%:R = 0%Re). { by apply /eqP. }
    rewrite H1 mulr0 subr0. apply /RltP.
    apply Rmult_lt_0_compat.
    * apply Re_complex_gt_0.
    * by apply /RltP.
Qed.

(** Coercion of the choice function from nat to complex ring **)
Lemma choice_to_ring: forall (n k:nat),
  (0<n)%N -> (k<=n)%N ->
  'C(n,k)%:R =
    ((n`!)%:R * ((n-k)`! )%:R^-1 * (k`! )%:R^-1) :>(complex R).
Proof.
intros.
rewrite bin_factd.
+ rewrite natr_div.
  - assert ((k`! * (n - k)`!)%:R = (k`!)%:R * ((n - k)`!)%:R :>complex R).
    { by rewrite mul_ring. } rewrite H1. clear H1.
    rewrite invrM.
    * by rewrite -div1r mulrA.
    * rewrite unitrE. apply /eqP.
      assert ( (k`!%:R / k`!%:R)  =
                mulc (invc (k`!%:R)) (k`!%:R) :> complex R).
      { by rewrite mulrC. } rewrite H1. apply mulVc.
      assert ((0%:C)%C = 0 :> complex R). { by []. } rewrite H2.
      apply fact_complex_ring_not_0.
    * rewrite unitrE. apply /eqP.
      assert ( ((n-k)`!%:R / (n-k)`!%:R)  =
                mulc (invc ((n-k)`!%:R)) ((n-k)`!%:R) :> complex R).
      { by rewrite mulrC. } rewrite H1. apply mulVc.
      assert ((0%:C)%C = 0 :> complex R). { by []. } rewrite H2.
      apply fact_complex_ring_not_0.
  - apply /dvdnP. exists 'C(n,k). by rewrite bin_fact.
  - rewrite mul_ring. rewrite unitrMr.
    * rewrite unitrE. apply /eqP.
      assert ( ((n-k)`!%:R / (n-k)`!%:R)  =
                mulc (invc ((n-k)`!%:R)) ((n-k)`!%:R) :> complex R).
      { by rewrite mulrC. } rewrite H1. apply mulVc.
      assert ((0%:C)%C = 0 :> complex R). { by []. } rewrite H2.
      apply fact_complex_ring_not_0.
    * rewrite unitrE. apply /eqP.
      assert ( (k`!%:R / k`!%:R)  =
                mulc (invc (k`!%:R)) (k`!%:R) :> complex R).
      { by rewrite mulrC. } rewrite H1. apply mulVc.
      assert ((0%:C)%C = 0 :> complex R). { by []. } rewrite H2.
      apply fact_complex_ring_not_0.
+ by [].
Qed.


Lemma pow_nat_ring: forall (m n:nat),
   m%:R ^+n = (m ^ n)%:R :>complex R.
Proof.
intros. induction n.
+ by [].
+ by rewrite exprS expnS mul_ring IHn.
Qed.

Lemma nat_complex_0_inv: forall (k:nat),
  Im ((k%:R)^-1)%C = 0%Re.
Proof.
intros. rewrite -div1r. rewrite Im_complex_div //=.
rewrite mul0r mul1r addr0 nat_complex_0. rewrite -RoppE.
assert ( (-0)%Re = 0%Re). { nra. } rewrite H.
by rewrite mul0r.
Qed.

Lemma nat_complex_Re: forall (k:nat),
  Re (k%:R) = k%:R :>R.
Proof.
intros. induction k.
+ by rewrite //=.
+ by rewrite -addn1 natrD Re_add IHk //= natrD.
Qed.

Lemma nat_complex_Re_inv: forall (k:nat),
  k%:R <> 0%Re -> Re (k%:R)^-1 = (k%:R^-1) :>R.
Proof.
intros. rewrite -div1r. rewrite Re_complex_div //=.
rewrite mul0r mul1r addr0 nat_complex_0.
rewrite !nat_complex_Re.
assert (0 ^+ 2 = 0 :>R). { by rewrite expr2 mulr0. }
rewrite H0 addr0 expr2. by rewrite div_prod.
Qed.

Lemma nat_ring_le: forall (n:nat),
  (0<= n)%N -> (0%Re <= n%:R)%Re.
Proof.
intros. induction n.
+ by apply /RleP.
+ rewrite -addn1 natrD. apply Rplus_le_le_0_compat.
  - by apply IHn.
  - apply Rlt_le. apply Rlt_0_1.
Qed.


Lemma nat_ring_lt: forall (n:nat),
  (0< n)%N -> (0%Re < n%:R)%Re.
Proof.
intros. induction n.
+ by apply /RltP.
+ rewrite -addn1 natrD. apply Rplus_le_lt_0_compat.
  - by apply nat_ring_le.
  - apply Rlt_0_1.
Qed.

Lemma pow_nat_ring_real: forall (m n:nat),
   m%:R ^+n = (m ^ n)%:R :>R.
Proof.
intros. induction n.
+ by [].
+ by rewrite exprS expnS mul_ring_real IHn.
Qed.


Lemma nat_ring_mn_le: forall (m n:nat),
  (m<= n)%N -> (m%:R <= n%:R)%Re.
Proof.
intros. induction n.
+ rewrite leqn0 in H. assert ( m = 0%N). { by apply /eqP. }
  rewrite H0. nra.
+ rewrite leq_eqVlt in H.
  assert ( (m == n.+1) \/ (m < n.+1)%N).
  { by apply /orP. } destruct H0.
  - assert ( m = n.+1). { by apply /eqP. }
    rewrite H1. nra.
  - assert ( (m <=n)%N). { by []. }
    specialize (IHn H1).
    rewrite -addn1 natrD. apply Rle_trans with n%:R.
    * apply IHn.
    * rewrite -RplusE.
      assert (n%:R = (n%:R + 0)%Re). { nra. }
      rewrite H2.
      assert ((n%:R + 0 + 1%:R)%Re = (n%:R + 1%:R)%Re).
      { nra. } rewrite H3. apply Rplus_le_compat.
      nra. apply Rlt_le. apply Rlt_0_1.
Qed.

Lemma fact_pow_le: forall (n k:nat),
  (k <= n)%N -> ((n`!%:R / (n - k)`!%:R)%Ri <= (n ^ k)%:R)%Re.
Proof.
intros.
assert ( (k==n) \/ (k <n)%N). { apply /orP. by rewrite -leq_eqVlt. }
destruct H0.
- assert ( k = n). { by apply /eqP. } rewrite H1.
  assert ( (n - n)%N = 0%N).
  { apply /eqP. assert ((n<=n)%N). { by []. } by rewrite /leq. }
  rewrite H2 fact0 divr1. apply nat_ring_mn_le.
  apply n_fact_le_pow.
- clear H. induction k.
  + rewrite subn0 expn0. rewrite -RdivE.
    - assert ((n`!%:R / n`!%:R )%Re = 1 :>R).
      { apply Rinv_r.
        assert ( (0 < n`!%:R)%Re -> n`!%:R <> 0%Re). { nra. }
        apply H. apply fact_ring_gt_0.
      } rewrite H. by apply /RleP.
    - apply /eqP.
      assert ( (0 < n`!%:R)%Re -> n`!%:R <> 0%Re). { nra. }
      apply H. apply fact_ring_gt_0.
  + assert ( (k <n)%N).
    { assert ((0<=n)%N). { by []. }
      assert ( (0%N == n) \/ (0< n)%N).
      { apply /orP. by rewrite -leq_eqVlt. } destruct H1.
      + assert (n= 0%N). { apply /eqP. by rewrite eq_sym. }
        rewrite H2 in H0. by [].
      + apply ltn_trans with n.-1.
        - by rewrite ltn_predRL.
        - clear H. by rewrite ltn_predL.
    } specialize (IHk H).
    rewrite expnS mul_ring_real. rewrite -RdivE. rewrite -RmultE.
    - assert (n`!%:R  = (n`!%:R * ((n-k)%:R / (n-k)%:R))%Re).
      { assert (((n-k)%:R / (n-k)%:R)%Re = 1).
        { apply Rinv_r.
          assert ( (0 < (n - k)%:R)%Re -> (n - k)%:R <> 0%Re). { nra. }
          apply H1. apply nat_ring_lt. by rewrite subn_gt0.
        } rewrite H1.
        by rewrite RmultE mulr1.
      } rewrite H1.
      assert ((n`!%:R * ((n - k)%:R / (n - k)%:R) / (n - k.+1)`!%:R)%Re=
                ((n-k)%:R * (n`!%:R / (n - k)`!%:R))%Re).
      { assert ( (n`!%:R * ((n - k)%:R / (n - k)%:R) / (n - k.+1)`!%:R)%Re =
                  ((n`!%:R * (n - k)%:R) / ((n - k)%:R * (n - k.+1)`!%:R))%Re).
        { rewrite -Rmult_assoc.
          assert ((n`!%:R * (n - k)%:R * / (n - k)%:R / (n - k.+1)`!%:R)%Re =
                  ((n`!%:R * (n - k)%:R )* ( / (n - k)%:R * / (n - k.+1)`!%:R))%Re).
          { nra. } rewrite H2.
          assert ( (/ (n - k)%:R * / (n - k.+1)`!%:R)%Re =
                    (/ ((n - k)%:R * (n - k.+1)`!%:R))%Re).
          { rewrite -Rinv_mult.
            + by [].
          } rewrite H3. nra.
        } rewrite H2.
        assert ((n - k)`!%:R = ((n-k.+1).+1)`!%:R :>R).
        { assert ( (n-k)%N = ((n-k.+1).+1)%N).
          { assert ( (0 < (n-k))%N). { by rewrite subn_gt0. }
            rewrite -[LHS]prednK.
            + assert ((n - k.+1)%N = (n-k).-1).
              { by rewrite subnS. } by rewrite H4.
            + by [].
          } rewrite H3. by rewrite factS.
        } rewrite H3 factS.
        assert ( (n-k)%N = ((n-k.+1).+1)%N).
        { assert ( (0 < (n-k))%N). { by rewrite subn_gt0. }
          rewrite -[LHS]prednK.
          + assert ((n - k.+1)%N = (n-k).-1).
            { by rewrite subnS. } by rewrite H5.
          + by [].
        } rewrite -H4. rewrite mul_ring_real -RmultE.
        nra.
      } rewrite H2. clear H2.
      apply Rmult_le_compat.
      * apply Rlt_le. apply nat_ring_lt. by rewrite subn_gt0.
      * apply Rlt_le.  apply Rmult_lt_0_compat.
        { apply fact_ring_gt_0. }
        { apply Rinv_0_lt_compat. apply fact_ring_gt_0. }
      * apply nat_ring_mn_le. apply leq_subr.
      * rewrite RdivE.
        { apply IHk. }
        { assert ( (0 < (n - k)`!%:R)%Re -> (n - k)`!%:R <> 0%Re). { nra. }
          apply /eqP. apply H2. apply fact_ring_gt_0.
        }
    - apply /eqP.
      assert ( (0 < (n - k.+1)`!%:R)%Re -> (n - k.+1)`!%:R <> 0%Re). { nra. }
      apply H1. apply fact_ring_gt_0.
Qed.

(** Proof that n C k is less than equal to n^k / k! **)
Lemma choice_to_ring_le: forall (n k:nat),
  (0<n)%N -> (k<=n)%N ->
  ('C(n,k)%:R <= (n%:R^+k / (k`!)%:R) :> complex R) .
Proof.
intros. rewrite choice_to_ring.
+ rewrite lecE. apply /andP.
  split.
  - apply /eqP. rewrite !Im_complex_prod.
    rewrite !nat_complex_0 mul0r addr0.
    rewrite !Re_complex_prod !nat_complex_0 mul0r subr0.
    rewrite !pow_nat_ring !nat_complex_0 mul0r addr0.
    rewrite !nat_complex_0_inv mulr0.
    by rewrite -mulrA !mulr0 add0r mul0r.
  - rewrite !Re_complex_prod !nat_complex_0 mul0r subr0.
    rewrite !Im_complex_prod !nat_complex_0 !nat_complex_0_inv.
    rewrite !mulr0 !subr0. rewrite nat_complex_Re !nat_complex_Re_inv.
    * rewrite pow_nat_ring nat_complex_Re. apply /RleP.
      apply Rmult_le_compat_r.
      ++ rewrite -div1r -RdivE.
         - assert ((1 / k`!%:R)%Re = (/ k`!%:R)%Re). { nra. }
           rewrite H1. apply Rlt_le. apply Rinv_0_lt_compat.
           apply fact_ring_gt_0.
         - apply /eqP. assert ( (0< k`!%:R)%Re -> k`!%:R <> 0%Re). { nra. }
           apply H1. apply fact_ring_gt_0.
      ++ by apply fact_pow_le.
    * assert ( (0 < k`!%:R)%Re -> k`!%:R <> 0%Re).
      { nra. } apply H1. apply fact_ring_gt_0.
    * assert ( (0 < (n-k)`!%:R)%Re -> (n-k)`!%:R <> 0%Re).
      { nra. } apply H1. apply fact_ring_gt_0.
+ by [].
+ by [].
Qed.


Lemma C_mod_le_rel_c : forall (x y: complex R),
  (0 <= Re x)%Re -> (0 <= Re y)%Re ->
  (x <= y)%C -> C_mod x <= C_mod y.
Proof.
intros. rewrite /C_mod. apply /RleP. apply sqrt_le_1.
+ rewrite -!RpowE. nra.
+ rewrite -!RpowE. nra.
+ rewrite lecE in H1.
  assert ((Im y == Im x) /\ (Re x <= Re y)).
  { by apply /andP. } destruct H2.
  assert (Im y = Im x). { by apply /eqP. } rewrite H4.
  apply Rplus_le_compat_r. rewrite -!RpowE.
  assert ( Rsqr (Re x) = (Re x ^ 2)%Re).
  { rewrite /Rsqr. nra. } rewrite -H5.
  assert ( Rsqr (Re y) = (Re y ^ 2)%Re).
  { rewrite /Rsqr. nra. } rewrite -H6.
  apply Rsqr_incr_1.
  - by apply /RleP.
  - by [].
  - by [].
Qed.

(** If |x| < 1, then \lim_{m \to \infty} ||x^m+1|| = 0 **)
Lemma is_lim_seq_geom_pow: forall (x : R),
  Rabs x < 1 -> is_lim_seq (fun m:nat => (x^m.+1)%Re) 0%Re.
Proof.
intros.
rewrite -is_lim_seq_spec /is_lim_seq'.
intros. rewrite /eventually.
assert (forall y: R, (0 < y)%Re ->
          exists N:nat, (forall n:nat, (n >=N)%coq_nat ->
          (Rabs ( x ^n) < y)%Re)).
{ apply pow_lt_1_zero. by apply /RltP. }
specialize (H0 eps).
assert ( (0 < eps)%Re). { apply posreal_cond. }
specialize (H0 H1). destruct H0 as [N H0].
exists N. intros.
specialize (H0 n.+1).
assert ((n.+1 >= N)%coq_nat). { lia. } specialize (H0 H3).
assert ((x ^ n.+1 - 0)%Re = (x ^ n.+1)%Re). { nra. }
by rewrite H4.
Qed.

Lemma r_pow_n_gt_0: forall (x:R) (n:nat),
  (0 < x)%Re -> (0 < x^n)%Re.
Proof.
intros. induction n.
+ rewrite RpowE expr0. apply Rlt_0_1.
+ rewrite RpowE exprS. apply Rmult_lt_0_compat.
  - nra.
  - rewrite -RpowE. nra.
Qed.

(** Proof that their exists a real between two real numbers **)
Lemma exist_real_between: forall (a b:R),
  (a < b)%Re ->
  exists c:R, (a < c)%Re /\ (c < b)%Re.
Proof.
intros. exists ((a+b)/2)%Re. nra.
Qed.

(** Proof that for a decreasing geometric series, the n^th term
  is smaller than or equal to the first term of the series **)
Lemma geom_series: forall (a: nat -> R) (n N:nat) (r:R),
  (0 < r)%Re -> (r < 1)%Re ->
  (N <= n)%N ->
  (forall n:nat, (N <= n)%N -> (a n.+1 < a n * r)%Re) ->
  (a n <= a N / r ^ N * r ^ n)%Re .
Proof.
intros. induction n.
+ rewrite leqn0 in H1.
  assert ( N = 0%N). { by apply /eqP. } rewrite H3.
  assert ( (a 0%N / r ^ 0 * r ^ 0)%Re =
            (a 0%N * (/ r ^ 0 * r ^ 0))%Re).
  { nra. } rewrite H4.
  assert ( (/ r ^ 0 * r ^ 0)%Re = 1%Re).
  { apply Rinv_l.
    assert ( (0 < r ^0)%Re -> (r ^ 0)%Re <> 0%Re). { nra. }
    apply H5. rewrite RpowE. rewrite expr0. apply Rlt_0_1.
  } rewrite H5. nra.
+ assert ( (N == n.+1)%N \/ (N < n.+1)%N).
  { apply /orP. by rewrite -leq_eqVlt. } destruct H3.
  - assert ( N = n.+1). { by apply /eqP. } rewrite H4.
    assert ( (a n.+1 / r ^ n.+1 * r ^ n.+1)%Re =
            (a n.+1 * (/ r ^ n.+1 * r ^ n.+1))%Re).
    { nra. } rewrite H5.
    assert ( (/ r ^ n.+1 * r ^ n.+1)%Re = 1%Re).
    { apply Rinv_l.
      assert ( (0 < r ^n.+1)%Re -> (r ^ n.+1)%Re <> 0%Re). { nra. }
      apply H6. by apply r_pow_n_gt_0.
    } rewrite H6. nra.
  - assert ( (N<=n)%N). { by []. }
    specialize (IHn H3).
    apply Rle_trans with (a n * r)%Re.
    * apply Rlt_le, H2, H4.
    * assert ( (r ^ n.+1)%Re = ( r ^ n * r)%Re).
      { rewrite !RpowE. by rewrite exprS mulrC. }
      rewrite H5.
      assert ( (a N / r ^ N * (r ^ n * r))%Re =
                ((a N / r ^ N * r ^ n )* r)%Re). { nra. }
      rewrite H6. apply Rmult_le_compat_r; nra.
Qed.


(*** Ratio test for convergence of sequences ***)
Lemma ratio_test: forall (a: nat -> R) (L:R),
  (0 < L /\ L < 1) ->
  (forall n:nat, (0 < a n)%Re) ->
  (is_lim_seq ( fun n:nat => ((a (n.+1))/ (a n))%Re) L) ->
  is_lim_seq (fun n: nat => a n) 0%Re.
Proof.
intros. destruct H.
assert ( exists r:R, (L < r)%Re /\ (r < 1)%Re).
{ apply exist_real_between. by apply /RltP.  }
destruct H3 as [r H3]. destruct H3.
rewrite <-is_lim_seq_spec in H1.
rewrite /is_lim_seq' in H1.
assert ( (0 < r-L)%Re). { nra. }
specialize (H1 (mkposreal (r-L)%Re H5)).
rewrite /eventually in H1. destruct H1 as [N H1].

rewrite -is_lim_seq_spec /is_lim_seq'. intros.

assert (is_lim_seq (fun n:nat => (r^n)%Re) 0%Re).
{ apply is_lim_seq_geom. rewrite Rabs_right. nra.
  apply Rle_ge, Rlt_le. apply Rlt_trans with L.
  + by apply /RltP.
  + nra.
} rewrite <-is_lim_seq_spec in H6. rewrite /is_lim_seq' in H6.
assert ( (0 < eps * (r^N/ a N))%Re).
{ apply Rmult_lt_0_compat.
  + apply posreal_cond.
  + apply Rmult_lt_0_compat.
    - apply r_pow_n_gt_0.
      apply Rlt_trans with L.
      * by apply /RltP.
      * nra.
    - by apply Rinv_0_lt_compat.
} specialize (H6 (mkposreal (eps* (r^N/ a N))%Re H7)).
unfold eventually in H6. destruct H6 as [M H6].

rewrite /eventually.
exists (maxn N M). intros.
assert ( (N <= n)%coq_nat).
{ apply /ssrnat.leP. assert ( (maxn N M <= n)%N). { by apply /ssrnat.leP. }
  rewrite geq_max in H9.
  assert ((N <= n)%N /\ (M <= n)%N). { by apply /andP. }
  destruct H10. by [].
}

assert ( (M <= n)%coq_nat).
{ apply /ssrnat.leP. assert ( (maxn N M <= n)%N). { by apply /ssrnat.leP. }
  rewrite geq_max in H10.
  assert ((N <= n)%N /\ (M <= n)%N). { by apply /andP. }
  destruct H11. by [].
}

specialize (H6 n H10).

assert ( (a n - 0)%Re = a n). { nra. } rewrite H11.

assert (forall n:nat , (N<=n)%coq_nat -> (a n.+1 < a n * r)%Re).
{ intros. specialize (H1 n0 H12).
  assert ( (Rabs (a n0.+1 / a n0 - L) <
             {| pos := r - L; cond_pos := H5 |})%Re ->
              (Rabs (a n0.+1 / a n0 - L) < (r-L))%Re).
  { auto. } specialize (H13 H1). clear H1.
  apply Rabs_def2 in H13. destruct H13.
  apply Rplus_lt_reg_r in H1.
  assert ( a n0.+1 = (a n0 * (a n0.+1 / a n0))%Re).
  { assert ( (a n0 * (a n0.+1 / a n0))%Re = (a n0.+1 * (a n0 * / a n0))%Re).
    { nra. } rewrite H14. rewrite Rinv_r.
    + nra.
    + assert ((0 < a n0)%Re -> a n0 <> 0%Re). { nra. } apply H15. apply H0.
  } rewrite H14. apply Rmult_lt_compat_l.
  + apply H0.
  + nra.
}

assert ((Rabs (r ^ n - 0) <
          {| pos := (eps * (r ^ N / a N)); cond_pos := H7 |})%Re ->
          (Rabs (r ^ n - 0) < (eps * (r ^ N / a N)))%Re).
{ auto. } specialize (H13 H6). clear H6.

assert ((r ^ n - 0)%Re = (r ^ n)%Re). { nra. } rewrite H6 in H13.
clear H6.

rewrite Rabs_right.
+ apply Rle_lt_trans with ((a N / (r^N)) * (r^n))%Re.
  - apply geom_series.
    * apply Rlt_trans with L.
        { by apply /RltP. }
        { nra. }
    * nra.
    * by apply /ssrnat.leP.
    * intros. apply H12. by apply /ssrnat.leP.
  - rewrite Rabs_right in H13.
    * assert ((((a N / r ^ N) * (/ (a N / r ^ N)))%Re * eps)%Re = eps).
      { assert ( ((a N / r ^ N) * (/ (a N / r ^ N)))%Re = 1%Re).
        { apply Rinv_r.
          assert ( (0< (a N / r ^ N))%Re -> (a N / r ^ N)%Re <> 0%Re).
          { nra. } apply H6. apply Rmult_lt_0_compat.
          + by [].
          + apply Rinv_0_lt_compat. apply r_pow_n_gt_0.
            apply Rlt_trans with L.
            * by apply /RltP.
            * nra.
        } rewrite H6. nra.
     } rewrite -H6.
     assert ((a N / r ^ N * / (a N / r ^ N) * eps)%Re =
              ((a N / r ^ N) * ( eps * ( / (a N / r ^ N))))%Re).
     { nra. } rewrite H14. apply Rmult_lt_compat_l.
     + apply Rmult_lt_0_compat.
       - by [].
       - apply Rinv_0_lt_compat. apply r_pow_n_gt_0.
         apply Rlt_trans with L.
         * by apply /RltP.
         * nra.
     + assert ( (/ (a N / r ^ N))%Re = (r ^ N / a N)%Re).
       { rewrite Rinv_mult.
         + rewrite Rinv_inv.
           - nra.
       } by rewrite H15.
    * apply Rle_ge. apply Rlt_le. apply r_pow_n_gt_0.
      apply Rlt_trans with L.
      * by apply /RltP.
      * nra.
+ apply Rle_ge, Rlt_le, H0.
Qed.

(** Proof: \lim_{m \to \infty} a n = 1 -->
           \lim_{m \to \infty} (a n)^k = 1 **)
Lemma is_lim_pow_const: forall (a : nat -> R) (k:nat),
  is_lim_seq (fun n:nat => a n) 1%Re ->
  is_lim_seq (fun n:nat => ((a n)^k)%Re) 1%Re.
Proof.
intros. induction k.
+ apply is_lim_seq_ext  with (fun n:nat => 1%Re).
  - intros. by rewrite RpowE expr0.
  - apply is_lim_seq_const.
+ apply is_lim_seq_ext with (fun n:nat => ((a n) * (a n)^k)%Re).
  - intros. rewrite !RpowE. by rewrite !RmultE -exprS.
  - assert ( 1%Re = (1*1)%Re). { nra.  } rewrite H0.
    by apply is_lim_seq_mult'.
Qed.

(** Comptability between the INR from standard reals and
  the mathcomp coercion from nats to reals **)
Lemma INR_eq:forall (n:nat),
  / (INR n + 1) = (1 / n.+1%:R)%Re.
Proof.
intros. assert ((1 / n.+1%:R)%Re = (/ n.+1%:R)%Re). { nra. }
rewrite H. clear H.
assert ( (INR n + 1) = n.+1%:R).
{ induction n.
  + by rewrite add0r.
  + rewrite -addn1 plus_INR.
    assert (INR 1 = 1%Re). { by []. } rewrite H.
    rewrite RplusE IHn. rewrite -addn1.
    assert ( (n + 1).+1 = ((n+1)+1)%N). { by rewrite !addn1. }
    rewrite H0. by rewrite [RHS]natrD.
} by rewrite -H.
Qed.

Lemma nat_pow_gt_0:forall (n k:nat),
  (0 < n.+1 ^ k)%N.
Proof.
intros. induction k.
+ by rewrite expn0.
+ rewrite expnS. rewrite muln_gt0. apply /andP.
  split.
  - apply ltn0Sn.
  - apply IHk.
Qed.


Lemma x_pow_not_zero:forall (y:R) (k:nat),
  y <> 0%Re -> (y ^ k)%Re <> 0.
Proof.
intros. induction k.
+ rewrite RpowE expr0.
  assert ( (0 < 1)%Re -> 1%Re <> 0%Re). { nra. } apply H0.
  nra.
+ rewrite RpowE exprS.
  apply Rmult_integral_contrapositive. split.
  - apply H.
  - by rewrite -RpowE.
Qed.


Lemma x_div_pow: forall (x y:R) (k:nat),
  y <> 0%Re -> (x^k  / y^k)%Re = ((x / y)^k)%Re .
Proof.
intros. induction k.
+ rewrite !RpowE !expr0. apply Rinv_r.
  assert ( (0 < 1)%Re -> 1%Re <> 0%Re). { nra. } apply H0.
  nra.
+ rewrite !RpowE !exprS. rewrite -!RmultE.
  rewrite -!RpowE.
  assert ((/ (y * y ^ k))%Re = (/y * / (y^k))%Re).
  { apply Rinv_mult.
  } assert ((x * x ^ k / (y * y ^ k))%Re  = (x * x ^ k * / (y * y ^ k))%Re).
  { nra. } rewrite H1 H0. nra.
Qed.

(** Proof: \lim_{m \to \infty} m^k x^m = 0. Proof done using
  ratio test for sequences and comparison with geometric sequences **)
Lemma lim_npowk_mul_to_zero: forall (x:R) (k:nat),
  (0 < x)%Re ->
  Rabs x < 1 ->
  is_lim_seq (fun m:nat => ((m.+1)%:R^k * x^ m.+1)%Re) 0%Re.
Proof.
intros.
assert ( let a:= (fun m:nat => ((m.+1)%:R^k * x^ m.+1)%Re) in
          (0 < (Rabs x) /\ (Rabs x) < 1) ->
          (forall n:nat, (0 < a n)%Re) ->
          (is_lim_seq ( fun n:nat => ((a (n.+1))/ (a n))%Re) (Rabs x)) ->
          is_lim_seq (fun n: nat => a n) 0%Re).
{ apply ratio_test. } apply H1.
+ split.
  - apply /RltP. apply Rabs_pos_lt. nra.
  - by apply H0.
+ intros. apply Rmult_lt_0_compat.
  - rewrite RpowE pow_nat_ring_real. apply nat_ring_lt, nat_pow_gt_0.
  - by apply r_pow_n_gt_0.
+ apply (is_lim_seq_ext (fun n:nat => ((1+ 1/n.+1%:R)^k * x)%Re)
          (fun n : nat => (n.+2%:R ^ k * x ^ n.+2 /
              (n.+1%:R ^ k * x ^ n.+1))%Re)).
  - intros.
    assert ( (n.+2%:R ^ k * x ^ n.+2 / (n.+1%:R ^ k * x ^ n.+1))%Re =
             ((n.+2%:R / n.+1%:R)^k * (x ^ n.+2 / x^n.+1))%Re).
    { assert ( (n.+2%:R ^ k * x ^ n.+2 / (n.+1%:R ^ k * (x ^ n.+1)))%Re =
               (n.+2%:R ^ k * x ^ n.+2 * (/ (n.+1%:R ^ k)) * (/ (x ^ n.+1)))%Re).
      { assert ((/ (n.+1%:R ^ k * x ^ n.+1))%Re  =
                ((/ (n.+1%:R ^ k)) * (/ (x ^ n.+1)))%Re).
        { apply Rinv_mult.
        }
        assert ((n.+2%:R ^ k * x ^ n.+2 / (n.+1%:R ^ k * x ^ n.+1))%Re =
                 (n.+2%:R ^ k * x ^ n.+2 * / (n.+1%:R ^ k * x ^ n.+1))%Re).
        { nra. } rewrite H3. rewrite H2. nra.
      } rewrite H2.
      assert ((n.+2%:R ^ k * x ^ n.+2 * / n.+1%:R ^ k * / x ^ n.+1)%Re =
              ((n.+2%:R ^ k / n.+1%:R^k) * (x^n.+2 / x^n.+1))%Re).
      { nra. } rewrite H3.
      assert ((n.+2%:R ^ k / n.+1%:R ^ k)%Re = ((n.+2%:R / n.+1%:R) ^ k)%Re).
      { apply x_div_pow. assert ( (0 < n.+1%:R)%Re -> n.+1%:R <> 0%Re). { nra. }
      apply H4. apply nat_ring_lt, ltn0Sn.
     } by rewrite H4.
   } rewrite H2.
   assert ((x ^ n.+2)%Re = (x * x ^ n.+1)%Re).
   { by rewrite !RpowE exprS. } rewrite H3.
   assert (((x * x ^ n.+1 / x ^ n.+1))%Re = x).
   { assert ((x ^ n.+1 / x ^ n.+1)%Re = 1%Re).
     { apply Rinv_r.
       assert ( (0 < (x ^ n.+1))%Re -> (x ^ n.+1)%Re <> 0%Re). { nra. }
       apply H4, r_pow_n_gt_0, H.
     }
     assert ((x * x ^ n.+1 / x ^ n.+1)%Re = (x * (x ^ n.+1 / x ^ n.+1))%Re).
     { nra. } rewrite H5 H4. nra.
   } rewrite H4. apply Rmult_eq_compat_r.
   assert ( n.+2%:R = (n.+1%:R + 1)%Re).
   { assert ( n.+2 = (n.+1 +1)%N). { by rewrite -addn1. } rewrite H5.
     by rewrite natrD.
   } rewrite H5.
   assert ((1 + 1 / n.+1%:R)%Re = ((n.+1%:R + 1) / n.+1%:R)%Re).
   { assert (((n.+1%:R + 1) / n.+1%:R)%Re = ((n.+1%:R  / n.+1%:R) + (1 / n.+1%:R))%Re).
     { nra. } rewrite H6.
     assert ((n.+1%:R / n.+1%:R )%Re = 1%Re).
     { apply Rinv_r. assert ( (0 < n.+1%:R)%Re -> n.+1%:R <> 0%Re). { nra. }
        apply H7. apply nat_ring_lt. apply ltn0Sn.
     } by rewrite H7.
   } by rewrite H6.
  - assert ( (Rabs x) = (1 * (Rabs x))%Re). { nra. } rewrite H2.
    apply is_lim_seq_mult'.
    * apply is_lim_pow_const.
      apply is_lim_seq_ext with (Rbar_loc_seq 1%Re).
      ++ intros. rewrite /Rbar_loc_seq. apply Rplus_eq_compat_l.
         by rewrite INR_eq.
      ++ apply is_lim_seq_Rbar_loc_seq.
    * rewrite Rabs_right.
      ++ apply is_lim_seq_const.
      ++ apply Rle_ge. by apply Rlt_le.
Qed.

(** Proof: \lim_{m \to \infty} x m = 0 -->
            \lim_{m \to \infty} (x m)^2 = 0 **)
Lemma lim_sqr_tends: forall (x: nat -> R),
  is_lim_seq (fun m:nat => x m) 0%Re ->
  is_lim_seq (fun m:nat => Rsqr (x m)) 0%Re.
Proof.
intros. rewrite -is_lim_seq_spec /is_lim_seq'.
intros. rewrite <-is_lim_seq_spec in H. unfold is_lim_seq' in H.
assert ( (0 < sqrt eps)%Re). { apply sqrt_lt_R0, posreal_cond. }
specialize (H (mkposreal (sqrt eps) H0)).
rewrite /eventually. rewrite /eventually in H.
destruct H as [N H]. exists N.
intros. specialize (H n). specialize (H H1).
assert ((Rabs (x n - 0) < {| pos := sqrt eps; cond_pos := H0 |})%Re ->
          (Rabs (x n - 0) <  sqrt eps)%Re ).
{ auto. } specialize (H2 H). clear H.
assert (((x n)² - 0)%Re = (x n)²). { nra. } rewrite H. clear H.
assert ((x n - 0)%Re = x n). { nra. } rewrite H in H2. clear H.
assert ( Rsqr (sqrt eps ) = eps).
{ rewrite Rsqr_sqrt. by []. apply Rlt_le. apply posreal_cond. }
rewrite -H.
assert ( Rabs (x n)² = Rsqr (Rabs (x n))).
{ unfold Rsqr. by rewrite Rabs_mult. } rewrite H3.
apply Rsqr_incrst_1.
+ apply H2.
+ apply Rabs_pos.
+ apply sqrt_pos.
Qed.



Lemma fact_ring_le_rel: forall (n:nat),
  (1%:R <= n.+1%:R ^+ n.+1 / (n.+1)`!%:R :>complex R).
Proof.
intros. rewrite lecE. apply /andP.
split.
+ apply /eqP. rewrite Im_complex_prod.
  rewrite !nat_complex_0 !nat_complex_0_inv mulr0 add0r.
  by rewrite pow_nat_ring nat_complex_0 mul0r.
+ rewrite Re_complex_prod //=. rewrite !pow_nat_ring.
  rewrite !nat_complex_Re !nat_complex_Re_inv.
  - rewrite !nat_complex_0 !nat_complex_0_inv mul0r subr0.
    rewrite -RdivE.
    * assert ( ((n.+1)`!%:R / (n.+1)`!%:R)%Re = 1).
      { apply Rinv_r.
        assert ( (0 < (n.+1)`!%:R)%Re -> (n.+1)`!%:R <> 0%Re).
        { nra. } apply H. apply fact_ring_gt_0.
      } apply /RleP.
      assert ( (((n.+1)`!%:R / (n.+1)`!%:R)%Re
                 <= (n.+1 ^ n.+1)%:R / (n.+1)`!%:R)%Re ->
                (1 <= (n.+1 ^ n.+1)%:R / (n.+1)`!%:R)%Re).
      { by rewrite H. } apply H0.
      apply  Rmult_le_compat_r.
      + apply Rlt_le. apply Rinv_0_lt_compat. apply nat_ring_lt.
        apply fact_gt0.
      + apply nat_ring_mn_le. apply n_fact_le_pow.
  - apply /eqP. assert ( ( 0< (n.+1)`!%:R)%Re -> (n.+1)`!%:R <> 0%Re).
    { nra. } apply H. apply fact_ring_gt_0.
+ assert ( ( 0< (n.+1)`!%:R)%Re -> (n.+1)`!%:R <> 0%Re).
  { nra. } apply H. apply fact_ring_gt_0.
Qed.



Lemma pow_complex_mod_div: forall (x: complex R) (m n:nat),
  x <> 0 -> (n<=m)%N -> (C_mod x)^+ (m-n)%N = ((C_mod x)^m / (C_mod x)^n)%Re.
Proof.
intros. rewrite exprB.
+ rewrite -RdivE.
  - by rewrite !RpowE.
  - apply /eqP. apply x_pow_n_not_0.
    assert ((0< C_mod x )%Re -> C_mod x  <> 0%Re).
    { nra. } apply H1. apply /RltP. by apply C_mod_gt_0.
+ by [].
+ rewrite unitrE. apply /eqP. rewrite -RdivE.
  - apply Rinv_r.
    assert ((0< C_mod x )%Re -> C_mod x  <> 0%Re).
    { nra. } apply H1. apply /RltP. by apply C_mod_gt_0.
  - apply /eqP.
    assert ((0< C_mod x )%Re -> C_mod x  <> 0%Re).
    { nra. } apply H1. apply /RltP. by apply C_mod_gt_0.
Qed.



Lemma pow_x_lt_1_rel: forall (x:R) (m n:nat),
  (0< x)%Re -> (x < 1)%Re -> (m >=n)%N -> (x^m <= x^n)%Re.
Proof.
intros. rewrite leq_eqVlt in H1.
assert ( (n == m) \/ (n < m)%N). { by apply /orP. }
destruct H2.
+ assert ( n=m). { by apply /eqP. } rewrite H3. nra.
+ assert ( (/ /x)%Re = x). { rewrite Rinv_inv. by []. }
  rewrite -H3. rewrite pow_inv.
  - assert ( ((/ / x) ^ n)%Re = (/ (/x)^n)%Re).
    { rewrite pow_inv. by []. }
    rewrite H4. apply Rlt_le. apply Rinv_lt_contravar.
    * apply Rmult_lt_0_compat; apply pow_lt; by apply Rinv_0_lt_compat.
    * apply Rlt_pow.
      ++ assert ( 1%Re = (/1)%Re). { nra. } rewrite H5.
         apply Rinv_lt_contravar.
         - nra.
         - nra.
         - by apply /ssrnat.ltP.
Qed.

Lemma index_leq: forall (k:nat) (a b:'I_k.+1),
  ((b-a)<=k)%N.
Proof.
intros.
assert ( (a <= k)%N). { apply leq_ord. }
assert ( (b <= k)%N). { apply leq_ord. }
apply leq_trans with b.
+ apply leq_subr.
+ by [].
Qed.


Lemma zero_pow_n:
  forall (n:nat), (0<n)%N -> 0^+n = 0 :> complex R.
Proof.
intros. induction n.
+ by [].
+ assert ((0<=n)%N). { by []. } rewrite leq_eqVlt in H0.
  assert ((0%N == n) \/ (0 < n)%N). { by apply /orP. }
  destruct H1.
  - assert (n= 0%N). { rewrite eq_sym in H1. by apply /eqP. }
    by rewrite H2.
  - specialize (IHn H1). rewrite exprS. by rewrite IHn mulr0.
Qed.


(** Proof that each term of the Jordan block tends to zero **)
Lemma each_entry_zero_lim:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  let sp := root_seq_poly (invariant_factors A) in
  let sizes := [seq x0.2.-1 | x0 <- sp] in
  forall i j: 'I_(size_sum sizes).+1,
  (forall i: 'I_(size_sum sizes).+1 , (C_mod (@nth _ (0 +i* 0)%C (lambda_seq A) i) < 1)%Re ) ->
  is_lim_seq
  (fun m: nat =>
    (C_mod (diag_block_mx sizes
              (fun n0 i1 : nat =>
               \matrix_(i2, j0) (('C(m.+1, j0 - i2))%:R *
                                     (nth
                                     (0, 0%N)
                                     (root_seq_poly
                                     (invariant_factors A))
                                     i1).1
                                     ^+
                                     (m.+1 - (j0 - i2)) *+
                                     (i2 <= j0))) i j))²) 0%Re.

Proof.
intros.
apply lim_sqr_tends.
assert ((exists k l (a: 'I_k.+1) (b: 'I_k.+1),
        (k <= size_sum sizes)%N /\  (l <= size_sum sizes)%N /\
        (forall m:nat, diag_block_mx sizes
          (fun n0 i1:nat => (Jordan_block (nth (0,0%N) (root_seq_poly
                                  (invariant_factors A)) i1).1 n0.+1)^+ m.+1) i j =
           (fun n0 i1:nat => (Jordan_block (nth (0,0%N) (root_seq_poly
                          (invariant_factors A)) i1).1 n0.+1)^+ m.+1 ) k l a b) /\
       (diag_block_mx sizes
          (fun n0 i1:nat => (Jordan_block (nth (0,0%N) (root_seq_poly
                                  (invariant_factors A)) i1).1 n0.+1)) i i =
          (fun n0 i1:nat => (Jordan_block (nth (0,0%N) (root_seq_poly
                                  (invariant_factors A)) i1).1 n0.+1)) k l a a)) \/
        (forall m:nat, diag_block_mx sizes
          (fun n0 i1:nat => (Jordan_block (nth (0,0%N) (root_seq_poly
                                  (invariant_factors A)) i1).1 n0.+1)^+ m.+1) i j =
                  0 :> (complex R))).
{ apply diag_destruct. }


(** Start working from here **)

rewrite -is_lim_seq_spec. unfold is_lim_seq'.
intros. unfold eventually.


assert (forall (k:nat) (x:R),
        (0 < x)%Re ->
        Rabs x < 1 ->
        is_lim_seq (fun m:nat => ((m.+1)%:R^k * x^ m.+1)%Re) 0%Re).
{ intros. by apply lim_npowk_mul_to_zero. }


assert (forall (x:R),
           Rabs x < 1 -> is_lim_seq (fun m:nat => (x^m.+1)%Re) 0%Re).
{ apply is_lim_seq_geom_pow. }

specialize (H1 n).
destruct H0.
+ destruct H0 as [k H0]. destruct H0 as [l H0].
  destruct H0 as [a H0]. destruct H0 as [b H0].
  destruct H0 as [size_k H0]. destruct H0 as [size_l H0].


  assert (forall i:'I_(size_sum sizes).+1, (nth (0 +i* 0)%C (lambda_seq A) i) = 0 \/ (nth (0 +i* 0)%C (lambda_seq A) i) <> 0).
  { intros.
    assert (((C_mod (@nth _ (0 +i* 0)%C (lambda_seq A) i0))%Re = 0%Re) \/  ((C_mod (@nth _ (0 +i* 0)%C (lambda_seq A) i0))%Re <> 0)%Re).
    { nra. } destruct H3.
    + left. by apply C_mod_eq_0.
    + right.  rewrite C_mod_gt_0. by apply C_mod_gt_not_zero.
  }

  destruct H0.
  assert (((nth (0, 0%N)
          (root_seq_poly (invariant_factors A))
          l).1 = 0) \/ ((nth (0, 0%N)
          (root_seq_poly (invariant_factors A))
          l).1 <> 0)).
  { assert(l = @inord (size_sum sizes) l).
    { by rewrite inordK. } rewrite H5.  specialize (H3 i).
      rewrite /lambda /lambda_seq in H3.
      rewrite (nth_map 0) in H3.
      + rewrite nth_ord_enum in H3.
        rewrite /Jordan_form in H3. rewrite H4 in H3.
        rewrite /Jordan_block in H3.  rewrite !mxE //= in H3.
        assert ((a == a :> nat) = true). {  by apply /eqP. }
        rewrite H6 //= in H3.
        assert (a.+1 == a :> nat = false).
        { by apply gtn_eqF. } rewrite H7 //= in H3.
        rewrite mulr0n mulr1n addr0 in H3. by rewrite H5 in H3.
     + rewrite size_enum_ord.
        apply ltn_ord.
  }
  destruct H5.
  - exists n.+1.
    intros. specialize (H0 n0). rewrite -diag_ext in H0.
    rewrite Jordan_expn in H0. rewrite H0.
    rewrite H5. rewrite mxE. rewrite zero_pow_n.
    * rewrite mulr0 mul0rn C_mod_0.
      assert ((0-0)%Re = 0%Re). { nra.  } rewrite H7 Rabs_R0.
      apply posreal_cond.
    * assert (((b-a)%N < n0.+1)%N).
      { apply leq_ltn_trans with n.+1.
        + apply leq_trans with k.
          - by apply index_leq.
          - apply leqW.
            assert ((size_sum sizes) = n).
            { apply /eqP. rewrite -eqSS. apply /eqP. by rewrite total_eigen_val. } by rewrite -H7.
        + rewrite ltnS. assert ((n.+1 <= n0)%N). { by apply /ssrnat.leP. }
          by [].
      } by rewrite subn_gt0.

    remember ((nth (0, 0%N) (root_seq_poly (invariant_factors A)) l).1) as lam.
  - specialize (H1 (C_mod lam)).
    specialize (H2 (C_mod lam)).

    assert ( (0 < C_mod lam)%Re).
    { apply /RltP. by apply C_mod_gt_0. }
    specialize (H1 H6).

    assert ((Rabs (C_mod lam) < 1)).
    { apply /RltP. rewrite Rabs_right.
      + specialize (H i).
        rewrite /lambda /lambda_seq in H.
        rewrite (nth_map 0) in H.
        - rewrite nth_ord_enum in H.
          rewrite /Jordan_form in H. rewrite H4 in H.
          rewrite /Jordan_block in H.  rewrite !mxE //= in H.
          assert ((a == a :> nat) = true). {  by apply /eqP. }
          rewrite H7 //= in H.
          assert (a.+1 == a :> nat = false).
          { by apply gtn_eqF. } rewrite H8 //= in H.
          rewrite mulr0n mulr1n addr0 in H. by apply H.
        - rewrite size_enum_ord.
          apply ltn_ord.
      + apply Rle_ge, C_mod_ge_0.
    }
    specialize (H1 H7). specialize (H2 H7).
    rewrite <-is_lim_seq_spec in H1. rewrite /is_lim_seq' in H1.
    rewrite <-is_lim_seq_spec in H2. rewrite /is_lim_seq' in H2.

    assert ( (0< (eps* (C_mod (lam) ^ n)))%Re).
    { apply Rmult_lt_0_compat.
      + apply posreal_cond.
      + apply pow_lt. apply /RltP. by apply C_mod_gt_0. (*apply eigen_not_zero. *)
    }

    specialize (H1 (mkposreal (eps* (C_mod (lam) ^ n))%Re H8)). specialize (H2 eps).
    rewrite /eventually in H1. rewrite /eventually in H2.

    destruct H1 as [N H1]. destruct H2 as [M H2].


    exists (maxn n.+1 (maxn M N)).
    intros.
    specialize (H1 n0). specialize (H2 n0).

    assert ( (N <= n0)%coq_nat).
    { apply /ssrnat.leP. assert ( (maxn n.+1 (maxn M N) <= n0)%N). { by apply /ssrnat.leP. }
      rewrite geq_max in H10.
      assert ((n < n0)%N /\ (maxn M N <= n0)%N). { by apply /andP. }
      destruct H11.
      rewrite geq_max in H12.
      assert ((M <= n0)%N /\ (N <= n0)%N). { by apply /andP. }
      destruct H13. by [].
    }

    assert ( (M <= n0)%coq_nat).
    { apply /ssrnat.leP. assert ( (maxn n.+1 (maxn M N) <= n0)%N). { by apply /ssrnat.leP. }
      rewrite geq_max in H11.
      assert ((n < n0)%N /\ (maxn M N <= n0)%N). { by apply /andP. }
      destruct H12.
      rewrite geq_max in H13.
      assert ((M <= n0)%N /\ (N <= n0)%N). { by apply /andP. }
      destruct H14. by [].
    }


    assert ( (n.+1 <= n0)%coq_nat).
    { apply /ssrnat.leP. assert ( (maxn n.+1 (maxn M N) <= n0)%N). { by apply /ssrnat.leP. }
      rewrite geq_max in H12.
      assert ((n < n0)%N /\ (maxn M N <= n0)%N). { by apply /andP. }
      by destruct H13.
    }


    specialize (H1 H10). specialize (H2 H11).

    assert (Hyp: (Rabs (n0.+1%:R ^ n * C_mod (lam) ^ n0.+1 - 0) <
                    {|
                    pos := eps * C_mod (lam) ^ n;
                    cond_pos := H8 |})%Re ->
                 (Rabs (n0.+1%:R ^ n * C_mod (lam) ^ n0.+1 - 0) <
                    eps * C_mod (lam) ^ n)%Re).
    { auto. } specialize (Hyp H1).


    specialize(H0 n0).
    rewrite -diag_ext in H0. rewrite Jordan_expn in H0. rewrite H0.
    rewrite mxE.
    rewrite real_sub_0r.

    assert (((b-a)%N < n0.+1)%N).
    { apply leq_ltn_trans with n.+1.
      + apply leq_trans with k.
        - by apply index_leq.
        - apply leqW.
          assert (size_sum sizes = n).
          { apply /eqP. rewrite -eqSS. apply /eqP. by rewrite total_eigen_val. } by rewrite -H13.
      + rewrite ltnS. assert ((n.+1 <= n0)%N). { by apply /ssrnat.leP. }
        by [].
    }

    apply Rle_lt_trans with
      (Rabs
       (C_mod
          ((((n0.+1)%:R^+(b-a)%N) * ((b-a)`!)%:R^-1) *
           (nth (0, 0%N) (root_seq_poly (invariant_factors A)) l).1
           ^+ (n0.+1 - (b - a)) *+ (a <= b)))).

        rewrite !Rabs_right.
        * assert ( (a<=b)%N \/ (a >=b)%N). { apply /orP. apply leq_total. }
          destruct H14.
          + rewrite H14. rewrite !mulr1n. rewrite !C_mod_prod. rewrite Heqlam.
            apply Rmult_le_compat_r.
            - apply C_mod_ge_0.
            - rewrite -C_mod_prod.
              assert ((b - a <= n0.+1)%N). { by apply ltnW. }
              apply /RleP. apply C_mod_le_rel_c.
                ++ rewrite nat_complex_Re. apply Rlt_le.
                   apply nat_ring_lt. by rewrite bin_gt0.
                ++ rewrite Re_complex_prod !pow_nat_ring.
                   rewrite !nat_complex_Re nat_complex_0 mul0r subr0.
                   rewrite nat_complex_Re_inv.
                   - apply Rlt_le. apply Rmult_lt_0_compat.
                     * apply nat_ring_lt. rewrite expn_gt0. apply /orP.
                       left. by [].
                     * rewrite -div1r -RdivE.
                       { assert ( (1 / (b - a)`!%:R)%Re = (/ (b - a)`!%:R)%Re).
                         { nra. } rewrite H16. apply Rinv_0_lt_compat.
                         apply nat_ring_lt. apply fact_gt0.
                       }
                       { apply /eqP. assert ( ( 0< (b - a)`!%:R)%Re -> (b - a)`!%:R <> 0%Re).
                          { nra. } apply H16. apply fact_ring_gt_0.
                       }
                   - assert ( ( 0< (b - a)`!%:R)%Re -> (b - a)`!%:R <> 0%Re).
                     { nra. } apply H16. apply fact_ring_gt_0.
                ++ by apply choice_to_ring_le.
          + assert ( (b==a)%N \/ (b<a)%N ).
            { apply /orP. by rewrite -leq_eqVlt. }
            destruct H15.
            - assert ( b = a). { by apply /eqP. }
              rewrite H16. clear H15. rewrite leqnn /=. rewrite !mulr1n. rewrite !C_mod_prod.
              rewrite Heqlam. apply Rmult_le_compat_r.
              * apply C_mod_ge_0.
              * rewrite H16 in H14.
                assert ((a-a)%N = 0%N).
                { apply /eqP. by rewrite /leq. }
                rewrite H15. rewrite bin0. rewrite fact0 expr0.
                rewrite invr1 !C_mod_1 mulr1. nra.
            - assert ((a <= b)%N = false). { by apply ltn_geF. }
              rewrite H16 /=. rewrite mulr0n. rewrite C_mod_0.
              nra.
      * apply Rle_ge,  C_mod_ge_0.
      * apply Rle_ge, C_mod_ge_0.
    - rewrite Rabs_right.
      * assert ( (a<=b)%N \/ (a >=b)%N). { apply /orP. apply leq_total. }
        destruct H14.
        { rewrite H14 //= !mulr1n.

          rewrite C_mod_prod. rewrite C_mod_div.
          + rewrite -RmultE. rewrite -RdivE.
            * assert (Rmult (C_mod (n0.+1%:R ^+ (b - a)) / C_mod (b - a)`!%:R)%Re
                       (C_mod
                         ((nth (0, 0%N) (root_seq_poly (invariant_factors A))
                             l).1 ^+ (n0.+1 - (b - a)))) =
                       (Rmult (C_mod (n0.+1%:R ^+ (b - a))*
                         C_mod
                           ((nth (0, 0%N) (root_seq_poly (invariant_factors A))
                               l).1 ^+ (n0.+1 - (b - a))) ) (/ C_mod (b - a)`!%:R)%Re)).
              { nra. } rewrite H15.
              assert ( ((eps * C_mod (b-a)`!%:R) * (/ C_mod (b - a)`!%:R))%Re =eps).
              { assert ( ((eps * C_mod (b-a)`!%:R) * (/ C_mod (b - a)`!%:R))%Re =
                          (eps * ((C_mod (b-a)`!%:R) * (/ C_mod (b - a)`!%:R)))%Re).
                { nra. } rewrite H16.
                assert ( ((C_mod (b - a)`!%:R * / C_mod (b - a)`!%:R))%Re = 1%Re).
                { apply Rinv_r.
                  assert ( (0 < C_mod (b - a)`!%:R)%Re -> C_mod (b - a)`!%:R <> 0%Re).
                  { nra. } apply H17. apply /RltP. apply C_mod_gt_0.
                  apply /eqP. apply fact_complex_ring_not_0.
                } rewrite H17. nra.
              } rewrite -H16. apply Rmult_lt_compat_r.
              ++ apply Rinv_0_lt_compat. apply /RltP. apply C_mod_gt_0.
                  apply /eqP. apply fact_complex_ring_not_0.
              ++ rewrite !C_mod_pow.
                 assert (C_mod
                           (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                              l).1 ^+ (n0.+1 - (b - a)) =
                          Rdiv (C_mod
                                 (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                    l).1 ^ n0.+1)
                               (C_mod
                                 (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                    l).1 ^ (b-a))).
                { apply pow_complex_mod_div.
                  + by rewrite -Heqlam.
                  + by apply ltnW.
                }
                rewrite H17. clear H17.
                assert (Rmult (C_mod n0.+1%:R ^+ (b - a))
                         (Rdiv (C_mod
                                (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                   l).1 ^ n0.+1)
                          (C_mod
                            (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                               l).1 ^ (b - a))) =
                          Rmult (Rmult (C_mod n0.+1%:R ^+ (b - a))
                                  (C_mod
                                    (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                       l).1 ^ n0.+1))
                          ( / (C_mod
                                (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                   l).1 ^ (b - a)))).
                { nra. } rewrite H17. clear H17.
                assert ( Rmult (Rmult (eps * C_mod (b - a)`!%:R)%Re
                            (C_mod
                               (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                  l).1 ^ (b - a)))
                        ( / (C_mod
                                (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                   l).1 ^ (b - a))) =
                        (eps * C_mod (b - a)`!%:R)%Re).
                { assert (Rmult (Rmult (eps * C_mod (b - a)`!%:R)%Re
                            (C_mod
                               (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                  l).1 ^ (b - a)))
                          ( / (C_mod
                                  (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                     l).1 ^ (b - a))) =
                            Rmult (eps * C_mod (b - a)`!%:R)%Re
                            (Rmult (C_mod
                               (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                  l).1 ^ (b - a))
                                ( / (C_mod
                                        (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                           l).1 ^ (b - a))))).
                  { nra. } rewrite H17.  clear H17.
                  assert ((Rmult (C_mod
                               (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                  l).1 ^ (b - a))
                                ( / (C_mod
                                        (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                           l).1 ^ (b - a)))) = 1%Re).
                  { apply Rinv_r. rewrite RpowE. apply x_pow_n_not_0. rewrite -Heqlam.
                    by apply C_mod_not_zero.
                  } rewrite H17. nra.
                } rewrite -H17. clear H17. apply Rmult_lt_compat_r.
                - apply Rinv_0_lt_compat. apply pow_lt. apply /RltP. rewrite -Heqlam. by apply C_mod_gt_0.
                - rewrite -RpowE.
                  assert (C_mod n0.+1%:R = n0.+1%:R :>R).
                  { rewrite /C_mod nat_complex_0 !expr2 mulr0 -RmultE.
                    assert ((Re n0.+1%:R * Re n0.+1%:R + 0)%Re =
                            (Re n0.+1%:R * Re n0.+1%:R)%Re). { nra. }
                    rewrite H17. rewrite sqrt_square.
                    + by rewrite nat_complex_Re.
                    + rewrite nat_complex_Re. apply Rlt_le. by apply nat_ring_lt.
                  } rewrite H17.
                  assert ((n0.+1%:R ^ n * C_mod (lam) ^ n0.+1 - 0)%Re =
                          (n0.+1%:R ^ n * C_mod (lam) ^ n0.+1)%Re).
                  { nra. } rewrite H18 in Hyp. clear H18 H17 H16 H15.
                  rewrite Rabs_right in Hyp.
                  * apply Rle_lt_trans with
                      (n0.+1%:R ^ n * C_mod (lam) ^ n0.+1)%Re.
                    ++ rewrite Heqlam. apply Rmult_le_compat_r.
                       - apply pow_le. apply C_mod_ge_0.
                       - apply Rle_pow.
                         * assert (1%Re = 1%:R). { auto. } rewrite H15.
                           by apply nat_ring_mn_le.
                         * apply /ssrnat.leP. apply leq_trans with k.
                           ++ by apply index_leq.
                           ++ assert (n = size_sum sizes).
                              { symmetry. apply /eqP. rewrite -eqSS. apply /eqP. by rewrite total_eigen_val. }
                              by rewrite H15.
                    ++ apply Rlt_le_trans with (eps * C_mod (lam) ^ n)%Re.
                       - apply Hyp. rewrite Heqlam.
                       - assert (Rmult (eps * C_mod (b - a)`!%:R)%Re
                                   (C_mod
                                     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                        l).1 ^ (b - a)) =
                                  Rmult eps (Rmult (C_mod (b - a)`!%:R)%Re
                                   (C_mod
                                     (nth (0, 0%N) (root_seq_poly (invariant_factors A))
                                        l).1 ^ (b - a)))). { nra. } rewrite H15. clear H12.
                          apply Rmult_le_compat_l.
                          * apply Rlt_le. apply posreal_cond.
                            assert ((C_mod (lam) ^ n)%Re  = (1 * C_mod (lam) ^ n)%Re).
                            { nra. } rewrite Heqlam in H12. rewrite H12. clear H12.
                            apply  Rmult_le_compat.
                            ++ nra.
                            ++ apply pow_le. apply C_mod_ge_0.
                            ++ assert (C_mod 1 = 1%Re). { apply C_mod_1. } rewrite -H12.
                               apply /RleP. apply C_mod_le_rel_c.
                               - rewrite //=. apply Rlt_le. apply Rlt_0_1.
                               - rewrite nat_complex_Re. apply Rlt_le. apply fact_ring_gt_0.
                               - rewrite lecE. apply /andP. split.
                                 * rewrite !nat_complex_0 //=.
                                 * rewrite !nat_complex_Re. assert (Re 1 = 1%Re). { by []. }
                                   rewrite H16. apply /RleP. assert (1%Re = 1%:R). { auto. }
                                   rewrite H17. apply nat_ring_mn_le. apply fact_gt0.
                          * apply pow_x_lt_1_rel.
                            ++ apply /RltP. rewrite -Heqlam. by apply C_mod_gt_0.
                            ++ specialize (H i). unfold lambda_seq in H.
                               rewrite (nth_map 0) in H.
                                + rewrite nth_ord_enum in H.
                                  rewrite /Jordan_form in H. rewrite H4 in H.
                                  rewrite /Jordan_block in H.  rewrite !mxE //= in H.
                                  assert ((a == a :> nat) = true). {  by apply /eqP. }
                                  rewrite H12 //= in H.
                                  assert (a.+1 == a :> nat = false).
                                  { by apply gtn_eqF. } rewrite H16 //= in H.
                                  rewrite mulr0n mulr1n addr0 in H. by rewrite -Heqlam.
                               + rewrite size_enum_ord.
                                  apply ltn_ord.
                            ++ apply leq_trans with k.
                               - by apply index_leq.
                               - assert (n = size_sum sizes).
                                 { symmetry. apply /eqP. rewrite -eqSS. apply /eqP. by rewrite total_eigen_val. }
                                 by rewrite H12.
                  * apply Rle_ge. apply Rlt_le. apply Rmult_lt_0_compat.
                    { apply pow_lt. by apply nat_ring_lt. }
                    { apply pow_lt. apply /RltP.  by apply C_mod_gt_0.
                 }
            * apply /eqP.
              assert ( (0 < C_mod (b - a)`!%:R)%Re -> C_mod (b - a)`!%:R <> 0%Re).
              { nra. } apply H15. apply /RltP. apply C_mod_gt_0.
              apply /eqP. apply fact_complex_ring_not_0.
          + apply /eqP.  apply fact_complex_ring_not_0.
        }
        { assert ( (b==a)%N \/ (b<a)%N ).
          { apply /orP. by rewrite -leq_eqVlt. }
          destruct H15.
          - assert ( b = a). { by apply /eqP. }
            rewrite H16. rewrite H16 in H14.
            assert ((a-a)%N = 0%N).
            { apply /eqP. by rewrite /leq. }
            rewrite !H17 //=. rewrite leqnn //=.
            rewrite mulr1n subn0 fact0 divr1 expr0 mul1r. rewrite C_mod_pow.
            rewrite -RpowE.
            assert ((C_mod (lam) ^ n0.+1 - 0)%Re =
                        (C_mod (lam) ^ n0.+1) %Re).
            { nra. } rewrite H18 in H2.
            rewrite Rabs_right in H2. rewrite Heqlam in H2.
            * by [].
            * apply Rle_ge. rewrite RpowE -C_mod_pow. apply C_mod_ge_0.
          - assert ((a <= b)%N = false). { by apply ltn_geF. }
            rewrite H16 /=. rewrite mulr0n. rewrite C_mod_0.
            apply posreal_cond.
        }
      * apply Rle_ge,C_mod_ge_0.
+ exists 0%N. intros. specialize (H0 n0). rewrite -diag_ext in H0.
  rewrite H0. rewrite C_mod_0.
  assert ((0 - 0)%Re = 0%Re). { nra. }
  rewrite H4. rewrite Rabs_R0. apply posreal_cond.
Qed.


(** If the limit of each term in the sum is 0 , then
    the limit of the sum is 0
**)
Lemma lim_sum_i:
  forall (n:nat) (x: 'I_n.+1 -> nat -> R),
  (forall i: 'I_n.+1, is_lim_seq (fun m: nat => x i m ) 0%Re) ->
  is_lim_seq (fun m:nat => \sum_j (x j m)) 0%Re.
Proof.
intros.
induction n.
+ apply (is_lim_seq_ext (fun m : nat =>  x ord_max m)
            (fun m : nat => \big[+%R/0]_j x j m)).
  - intros. rewrite big_ord_recr  big_ord0/=.
    by rewrite add0r.
  - by apply H.
+ apply (is_lim_seq_ext
           (fun m:nat => \big[+%R/0]_(i < n.+1) x (widen_ord (leqnSn n.+1) i)  m
              + x ord_max m)
            (fun m : nat => \big[+%R/0]_j x j m)).
  - intros. rewrite [RHS]big_ord_recr //=.
  - assert ( 0%Re = (0+0)%Re). { nra. } rewrite H0.
    apply is_lim_seq_plus'.
    * by apply IHn.
    * by apply H.
Qed.


(** If each entry of the Jordan block tends to zero, then the matrix
  norm defined as the sum of squares of the entries, tend to zero too **)
Lemma entry_sum_lim_zero :
forall (n:nat) (A: 'M[complex R]_n.+1),
(forall (i: 'I_n.+1), (C_mod (lambda A i) < 1)%Re) ->
is_lim_seq
  (fun m : nat =>
     (\big[+%R/0]_i0
         \big[+%R/0]_j
            (C_mod
               (diag_block_mx
                  [seq x0.2.-1
                     | x0 <- root_seq_poly
                               (invariant_factors A)]
                  (fun n0 i1 : nat =>
                   \matrix_(i2, j0) ('C(m.+1, j0 - i2)%:R *
                                     (nth
                                     (0, 0%N)
                                     (root_seq_poly
                                     (invariant_factors A))
                                     i1).1
                                     ^+
                                     (m.+1 - (j0 - i2)) *+
                                     (i2 <= j0))) i0 j))²)) 0%Re.
Proof.
intros.
apply lim_sum_i.
intros x.
apply lim_sum_i.
intros y. apply each_entry_zero_lim.
rewrite total_eigen_val. intros.
assert (@lambda _ A i = (nth (0 +i* 0)%C (lambda_seq A) i)).
{ by rewrite /lambda. } specialize (H i). rewrite H0 in H.
apply H.
Qed.



Lemma sqr_eps_pos: forall (x:posreal), (0 < Rsqr x)%Re.
Proof.
intros. apply Rsqr_pos_lt.
assert ((0<x)%Re). { apply posreal_cond. } nra.
Qed.

(** Proof: \lim_{m \to \infty} x m = 0 -->
           \lim_{m \to \infty} sqrt (x m) = 0 **)
Lemma lim_sqrt (x : nat -> R):
  (forall n:nat, (0<= x n)%Re) ->
  is_lim_seq (fun m: nat => x m)  0%Re->
  is_lim_seq (fun m:nat => sqrt (x m)) 0%Re.
Proof.
intros.
rewrite -is_lim_seq_spec. unfold is_lim_seq'.
intros. unfold eventually.
assert ( is_lim_seq (fun m: nat => x m)  0%Re <->
         is_lim_seq' (fun m: nat => x m)  0%Re).
{ symmetry. apply is_lim_seq_spec. } destruct H1.
specialize (H1 H0). unfold is_lim_seq' in H1.
specialize (H1 (mkposreal (Rsqr eps) (sqr_eps_pos eps))).
unfold eventually in H1.
destruct H1 as [N H1]. exists N.
intros. specialize (H1 n).
specialize (H1 H3).
assert ((x n - 0)%Re = (x n)%Re). { nra. } rewrite H4 in H1.
assert ( (Rabs (x n) < Rsqr eps)%Re). { auto. } clear H1.
assert ((sqrt (x n) - 0)%Re = sqrt (x n)). { nra. } rewrite H1.
clear H1 H4.
assert ( Rabs ( sqrt (x n)) = sqrt (x n)).
{ apply Rabs_right. apply Rle_ge. apply sqrt_pos. }
rewrite H1. clear H1.
assert ((Rabs (x n) < (Rsqr eps))%Re ->
          ((x n) < (Rsqr eps))%Re /\ (-(Rsqr eps) < (x n))%Re).
{ apply Rabs_def2. }
specialize (H1 H5).
apply Rsqr_incrst_0.
+ rewrite Rsqr_sqrt.
  - nra.
  - apply H.
+ apply sqrt_pos.
+ apply Rlt_le. apply posreal_cond.
Qed.


Lemma sum_x_ge_0:
  forall (n:nat) (x: 'I_n.+1 -> R),
  (forall i: 'I_n.+1, (0 <= x i)%Re ) ->
   (0<= \sum_j (x j))%Re.
Proof.
intros.
induction n.
+ rewrite big_ord_recr big_ord0 //=. rewrite add0r.
  apply H.
+ rewrite big_ord_recr //=. apply Rplus_le_le_0_compat.
  - apply IHn. intros. apply H.
  - apply H.
Qed.


Lemma mat_norm_converges:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  (forall (i: 'I_n.+1), (C_mod (@lambda _ A i) < 1)%Re) ->
  is_lim_seq (fun m:nat => matrix_norm (A^+m.+1)) 0%Re.
Proof.
intros.
assert (forall i:'I_n.+1, @eigenvalue (complex_fieldType _) n.+1 A (@lambda _ A i)).
{ apply Jordan_ii_is_eigen. }
have H1: exists2 V, V \in unitmx &
      mulmx V A = mulmx (conform_mx V (Jordan_form A)) V.
{ by apply V_exists. }
destruct H1 as [V H1 H2].
assert (A = mulmx (invmx V)
            (mulmx (conform_mx V (Jordan_form A)) V)).
{ have H3: mulmx (1%:M) A = A. { by apply mul1mx. }
  rewrite -[LHS]H3. clear H3.
  have H3: mulmx (invmx V) V = 1%:M.
  { by apply mulVmx. } rewrite -H3.
  rewrite -mulmxA. by apply matrix_eq1.
} rewrite H3.
apply (is_lim_seq_ext
          (fun m:nat => matrix_norm (mulmx (invmx V) (mulmx
            ((conform_mx V (Jordan_form A))^+m.+1) V)))
          (fun m:nat => matrix_norm ((mulmx (invmx V) (mulmx
            (conform_mx V (Jordan_form A)) V))^+m.+1)) ).
+ intros.
  assert (((invmx V *m (conform_mx V (Jordan_form A) *m V)) ^+ n0.+1) =
            (invmx V *m (conform_mx V (Jordan_form A) ^+ n0.+1 *m V))).
  { induction n0.
    - by rewrite !expr1.
    - have H4: n0.+2 = ((n0.+1)+1)%N.
      { by rewrite addn1. } rewrite H4.
      rewrite !exprD !expr1.
      rewrite IHn0.
      have H5: invmx V *m (conform_mx V (Jordan_form A) ^+ n0.+1 *
                  conform_mx V (Jordan_form A) *m V) =
                invmx V *m ((mulmx (conform_mx V (Jordan_form A) ^+ n0.+1) (1%:M)) *
                  conform_mx V (Jordan_form A) *m V).
      { by rewrite mulmx1. } rewrite H5. clear H5.
      have H5: mulmx V (invmx V) = 1%:M.
      { by apply mulmxV. } rewrite -H5.
      rewrite !mulmxA.
      have H6: invmx V *m conform_mx V (Jordan_form A)^+ n0.+1 *m V *m
                invmx V *m conform_mx V (Jordan_form A) *m V =
               invmx V *m conform_mx V (Jordan_form A)^+ n0.+1 *m V *m
                (invmx V *m conform_mx V (Jordan_form A) *m V).
      { by rewrite !mulmxA. } by rewrite H6.
  } by rewrite -H4.
  apply (is_lim_seq_le_le (fun m:nat => 0)
          (fun m : nat =>
                  matrix_norm
                       (invmx V *m (conform_mx V (Jordan_form A)
                                    ^+ m.+1 *m V)))
        (fun m : nat => ((matrix_norm (invmx V)) *
             (matrix_norm
               (conform_mx V (Jordan_form A)
                            ^+ m.+1 *m V)))%Re)).
  * intros. split.
    - apply matrix_norm.matrix_norm_ge_0.
    - apply matrix_norm.matrix_norm_prod.
  * apply is_lim_seq_const.
  * assert ( 0%Re = ((matrix_norm  (invmx V)) * 0)%Re).
    { nra. } rewrite H4.
    apply is_lim_seq_mult'.
    ++ apply is_lim_seq_const.
    ++ apply (is_lim_seq_le_le (fun m:nat => 0)
                (fun n0 : nat =>
                   matrix_norm
                     (conform_mx V (Jordan_form A) ^+ n0.+1 *m V))
              (fun n0 : nat =>
                   ((matrix_norm
                     (conform_mx V (Jordan_form A) ^+ n0.+1)) *
                   (matrix_norm V))%Re)).
        - intros. split.
          * by apply matrix_norm.matrix_norm_ge_0.
          * apply matrix_norm.matrix_norm_prod.
        - apply is_lim_seq_const.
        - assert ( 0%Re = (0 * matrix_norm V)%Re).
          { nra. } rewrite H5.
          apply is_lim_seq_mult'.
          * apply (is_lim_seq_le_le (fun m:nat => 0)
                    (fun n0 : nat =>
                       matrix_norm
                         (conform_mx V (Jordan_form A) ^+ n0.+1))
                    (fun n0 : nat =>
                       mat_norm
                         (conform_mx V (Jordan_form A) ^+ n0.+1))).
            ++ intros. split.
               - apply matrix_norm.matrix_norm_ge_0.
               - apply matrix_norm.mat_2_norm_F_norm_compat.
            ++ apply is_lim_seq_const.
            ++
          (** asserting J^m = diag[J^m_p1, J^m_p2, .. , J^m_ps] **)
           apply (is_lim_seq_ext
                  (fun m:nat => mat_norm  (conform_mx V
                      ((let sp:= root_seq_poly (invariant_factors A) in
                         let sizes := [seq (x.2).-1 | x <-sp] in
                           let blocks n i := (Jordan_block (nth (0,0%N) sp i).1 n.+1)^+m.+1 in
                              diag_block_mx sizes blocks))))
                  (fun n0 : nat =>
                      mat_norm  (conform_mx V (Jordan_form A) ^+ n0.+1))).
           intros.
           - apply mat_norm_eq.
             assert ((conform_mx V (Jordan_form A)) ^+ n0.+1 =
                      conform_mx V ((Jordan_form A) ^+ n0.+1)).
             { apply conform_mx_mat_power.
               apply /eqP. rewrite -eqSS. apply /eqP. by rewrite total_eigen_val.
             } rewrite H6.
             unfold Jordan_form. by rewrite exp_diag_block_S.

           (** now that we have powers for each Jordan block,
              define matrix norm as sums of absolute value
              of each entry in the matrix **)

          - apply (is_lim_seq_ext
                  (fun m: nat =>
                        (let sp := root_seq_poly (invariant_factors A) in
                         let sizes := [seq x0.2.-1 | x0 <- sp] in
                         let blocks :=
                           fun n0 i : nat =>
                           Jordan_block (nth (0, 0%N) sp i).1 n0.+1 ^+ m.+1 in
                         mat_norm (diag_block_mx sizes blocks)))

                    (fun m : nat =>
                   mat_norm
                     (conform_mx V
                        (let sp := root_seq_poly (invariant_factors A) in
                         let sizes := [seq x0.2.-1 | x0 <- sp] in
                         let blocks :=
                           fun n0 i : nat =>
                           Jordan_block (nth (0, 0%N) sp i).1 n0.+1 ^+ m.+1 in
                         diag_block_mx sizes blocks)))).
            * intros. simpl. rewrite matrix_norm_equality. by [].
              apply /eqP. rewrite -eqSS. apply /eqP. by rewrite total_eigen_val.
            * apply (is_lim_seq_ext
                      (fun m : nat =>
                       let sp := root_seq_poly (invariant_factors A) in
                       let sizes := [seq x0.2.-1 | x0 <- sp] in
                       let blocks :=
                         fun n0 i0 : nat =>
                         (\matrix_(i,j) ((('C(m.+1,j - i))%:R *
                            (((nth (0, 0%N) sp i0).1)^+ (m.+1 - (j - i)))) *+ (i <= j)))
                         in mat_norm (diag_block_mx sizes blocks))

                        (fun m : nat =>
                           let sp := root_seq_poly (invariant_factors A) in
                           let sizes := [seq x0.2.-1 | x0 <- sp] in
                           let blocks :=
                             fun n0 i0 : nat =>
                             Jordan_block (nth (0, 0%N) sp i0).1 n0.+1 ^+ m.+1 in
                           mat_norm (diag_block_mx sizes blocks))).
             { intros.  simpl.
               apply mat_norm_eq.
               by apply diag_ext.
             }

             (** Now that I have an expansion of Jordan block,
                 it's time to use the fact that |\lambda| < 1
                 and expand matrix_norm for the block diagonal
             **)
             { unfold mat_norm. apply lim_sqrt.
               + intros. apply sum_x_ge_0.
                 intros. apply sum_x_ge_0. intros.
                 apply Rsqr_ge_0. apply C_mod_ge_0.
               + by apply entry_sum_lim_zero.

             }
        ++ apply is_lim_seq_const.
Qed.




(** Define an eigenvector from the predicate of eigenvalue **)
Lemma eigen_vector_exists (n:nat) (i: 'I_n.+1) (A: 'M[complex R]_n.+1):
  @eigenvalue (complex_fieldType _) n.+1 A (@lambda n A i) ->
  exists v: 'rV_n.+1, (mulmx v A = (lambda A i) *: v) /\ (v != 0).
Proof.
intros.
assert ((exists2 v : 'rV_n.+1, v *m A = (lambda A i) *: v & v != 0)).
{ by apply /eigenvalueP. } destruct H0 as [v H0].
exists v. by split.
Qed.
