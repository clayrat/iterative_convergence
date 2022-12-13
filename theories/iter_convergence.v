Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp Require Import mxalgebra matrix all_field.
From mathcomp.analysis Require Import boolp Rstruct classical_sets signed.
From Coquelicot Require Import Lim_seq Rbar Hierarchy Lub.
Require Import complex_mat_vec_prop iter_necessity matrix_norm.

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

(** - (A B) = A * (-B) **)
Lemma Mopp_mult_r:
  forall (m n p:nat) (A: 'M[R]_(m.+1,n.+1)) (B: 'M[R]_(n.+1,p.+1)),
   oppmx (mulmx A B) = mulmx A (oppmx B).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite -mulrN.
Qed.

(** -(A B) = (-A) * B **)
Lemma Mopp_mult_l:
  forall (m n p:nat) (A: 'M[R]_(m.+1,n.+1)) (B: 'M[R]_(n.+1,p.+1)),
   oppmx (mulmx A B) = mulmx (oppmx A) B.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite mulNr.
Qed.

(** -(-A) = A **)
Lemma Mopp_opp :
  forall (m n:nat) (A: 'M[R]_(m.+1,n.+1)), oppmx (oppmx A) = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply opprK.
Qed.


Lemma inverse_A: forall (n:nat) (A: 'M[R]_n.+1),
  A \in unitmx ->
    mulmx A (invmx A) = 1%:M /\ mulmx (invmx A) A = 1%:M.
Proof.
intros. split.
+ by apply mulmxV.
+ by apply mulVmx.
Qed.

Lemma Mplus_0_r: forall (m n:nat) (A: 'M[R]_(m,n)),
  addmx A 0 = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. by rewrite addr0.
Qed.

Lemma Mplus_0_l: forall (m n:nat) (A: 'M[R]_(m,n)),
  addmx 0 A = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. by rewrite add0r.
Qed.

Lemma Mplus_opp_r: forall (m n:nat) (A: 'M[R]_(m,n)), addmx A (oppmx A) = 0.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply addrN.
Qed.

Lemma Mplus_opp_l: forall (m n:nat) (A: 'M[R]_(m,n)), addmx (oppmx A) A = 0.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply addNr.
Qed.


Fixpoint X_m (m n:nat) (x0 b: 'cV[R]_n.+1) (A1 A2: 'M[R]_n.+1) : 'cV[R]_n.+1:=
  match m with
  | O => x0
  | S p => ((- ((A1^-1) *m A2)) *m (X_m p x0 b A1 A2)) +
            ((A1^-1) *m b)
  end.


Definition one_vec_r (n:nat) : 'cV[R]_n.+1:=
  \col_(j < n.+1) 1%Re.


Definition e_i {n:nat} (i: 'I_n.+1): 'cV[complex R]_n.+1 :=
  \col_(j < n.+1) (if (i==j :> nat) then (1 +i* 0)%C else (0 +i* 0)%C).


Lemma base_sum_eq_zero:
forall (n:nat) (x: 'I_n.+1 -> 'cV[complex R]_n.+1) (P : pred 'I_n.+1) (x0: 'I_n.+1),
  (forall i, P i -> x i x0 0 = 0) ->
(\big[+%R/0]_(i < n.+1 | P i) x i) x0 0 = 0 .
Proof.
intros. apply big_rec.
+ by rewrite mxE.
+ intros. rewrite mxE. rewrite H1. specialize (H i H0). rewrite H. by rewrite addr0.
Qed.

Lemma base_exp: forall (n:nat) (x: 'cV[complex R]_n.+1),
  x = \big[+%R/0]_(i < n.+1) (x i 0 *: e_i i).
Proof.
intros.
apply matrixP. unfold eqrel. intros.
rewrite (bigD1 x0) //=.
rewrite !mxE //=.
assert (x0 == x0 :> nat = true). { apply eq_refl. }
rewrite H. rewrite mulr1.
assert ((\big[+%R/0]_(i < n.+1 | i != x0) (x i 0 *: e_i i)) x0 0 = 0).
{ apply base_sum_eq_zero. intros. rewrite !mxE //=.
  assert (i == x0 :> nat = false). { apply /eqP. by apply /eqP. }
  by rewrite H1 mulr0.
} assert (y = 0). { by rewrite ord1. } rewrite H1 H0.
by rewrite addr0.
Qed.


Lemma vec_sum_comp_eq:
forall (m n:nat) (x: 'I_m.+1 -> 'cV[complex R]_n.+1) (k: 'I_n.+1),
  (\big[+%R/0]_(i < m.+1) x i) k 0 = \big[+%R/0]_(i < m.+1) x i k 0.
Proof.
intros.
induction m.
+ rewrite !big_ord_recl //= !big_ord0. by rewrite !mxE.
+ rewrite big_ord_recr //=.
  assert (\big[+%R/0]_(i < m.+2) x i k 0 =
            \big[+%R/0]_(i < m.+1) x (widen_ord (leqnSn m.+1) i) k 0 +
             x ord_max k 0).
  { by rewrite big_ord_recr //=. } rewrite H.
  rewrite mxE. by rewrite IHm.
Qed.

Lemma big_sum_add_C: forall (n:nat) (u v: 'I_n.+1 -> complex R),
  \big[+%R/0]_j (u j) + \big[+%R/0]_j (v j) =
    \big[+%R/0]_j (u j + v j).
Proof.
intros. induction n.
+ simpl. rewrite !big_ord_recr //= !big_ord0. by rewrite !add0r.
+ simpl. rewrite big_ord_recr //=.
  assert (\big[+%R/0]_(j < n.+2) v j =
          \big[+%R/0]_(i < n.+1) v (widen_ord (leqnSn n.+1) i) +
            v ord_max).
  { by rewrite big_ord_recr //=. } rewrite H. clear H.
  assert (\big[+%R/0]_(j < n.+2) (u j + v j) =
          \big[+%R/0]_(i < n.+1) (u (widen_ord (leqnSn n.+1) i) +
                                  v (widen_ord (leqnSn n.+1) i)) +
          (u ord_max + v ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H. clear H.
  rewrite -IHn. rewrite -addrA. rewrite addrC. rewrite addrA.
  rewrite addrC. rewrite -addrA.
  assert ((u ord_max +
           (\big[+%R/0]_(i < n.+1) v
                                     (widen_ord
                                      (leqnSn n.+1) i) +
            v ord_max)) = ( (\big[+%R/0]_(i < n.+1) v
                           (widen_ord
                            (leqnSn n.+1) i) +
                              v ord_max)) +  u ord_max).
  { by rewrite addrC. } rewrite H. rewrite -addrA. rewrite addrA.
  assert (v ord_max + u ord_max = u ord_max + v ord_max). { by rewrite addrC. }
  by rewrite H0.
Qed.


Lemma matrix_vec_mul_add:
  forall (n:nat) (v1 v2: 'cV[complex R]_n.+1) (A: 'M[complex R]_n.+1),
  A*m (v1 + v2) = A *m v1 + A *m v2.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite big_sum_add_C. apply eq_big.
by []. intros.
rewrite !mxE. by rewrite mulrDr.
Qed.


Lemma matrix_vec_mul_add_sum:
  forall (m n:nat) (x: 'I_m.+1 -> 'cV[complex R]_n.+1) (A: 'M[complex R]_n.+1),
  A *m (\big[+%R/0]_(i < m.+1) x i) =
  \big[+%R/0]_(i < m.+1) (A *m x i).
Proof.
intros. induction m.
+ rewrite !big_ord_recl //= !big_ord0. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. by rewrite !addr0.
+ rewrite big_ord_recr //=.
  assert (\big[+%R/0]_(i < m.+2) (A *m x i) =
           \big[+%R/0]_(i < m.+1) (A *m (x (widen_ord (leqnSn m.+1) i))) +
            A *m x ord_max).
  { by rewrite big_ord_recr //=. } rewrite H.
  rewrite matrix_vec_mul_add. by rewrite IHm.
Qed.


Lemma vec_norm_add_le:
  forall (n:nat) (v1 v2 : 'cV[complex R]_n.+1),
  vec_norm_C (v1 + v2) <= vec_norm_C v1 + vec_norm_C v2.
Proof.
intros. rewrite /vec_norm_C. apply /RleP.
rewrite -RplusE.
apply Rsqr_incr_0_var.
+ rewrite Rsqr_sqrt.
  - rewrite Rsqr_plus. rewrite !Rsqr_sqrt.
    * apply Rle_trans with
       (\big[+%R/0]_l (Rsqr (C_mod (v1 l 0)) + Rsqr (C_mod (v2 l 0)) + 2 * C_mod (v1 l 0) * C_mod (v2 l 0))).
      ++ apply /RleP. apply big_sum_ge_ex_abstract.
         intros. rewrite mxE.
         apply Rle_trans with (Rsqr (C_mod (v1 i 0) + C_mod (v2 i 0))).
         -- apply Rsqr_incr_1.
            * apply /RleP. apply C_mod_add_leq.
            * apply C_mod_ge_0.
            * apply Rplus_le_le_0_compat; apply C_mod_ge_0.
         -- rewrite Rsqr_plus. rewrite -!RplusE -!RmultE. apply Rle_refl.
      ++ rewrite -!big_sum_add. rewrite -!RplusE.
         apply Rplus_le_compat_l.
         assert (\big[+%R/0]_j
                    (2 * C_mod (v1 j 0) * C_mod (v2 j 0))%Ri =
                  2 * \big[+%R/0]_j (C_mod (v1 j 0) * C_mod (v2 j 0))%Ri).
         { rewrite [RHS]big_distrr //=. apply eq_big. by []. intros. by rewrite mulrA. }
         rewrite H. clear H.
         rewrite Rmult_assoc. apply Rmult_le_compat_l.
         - nra.
         - rewrite -sqrt_mult.
           * apply Rsqr_incr_0_var.
             - rewrite Rsqr_sqrt.
               ++ apply /RleP. apply big_sqr_le.
                  -- intros. apply /RleP. apply C_mod_ge_0.
                  -- intros. apply /RleP. apply C_mod_ge_0.
               ++ apply Rmult_le_compat_0.
                  -- apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
                  -- apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
             - apply sqrt_pos.
           * apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
           * apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
    * apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
    * apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
  - apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
+ apply Rplus_le_le_0_compat; apply sqrt_pos.
Qed.

Lemma vec_norm_add_le_sum:
  forall (m n:nat) (x: 'I_m.+1 -> 'cV[complex R]_n.+1),
  vec_norm_C (\big[+%R/0]_(i < m.+1) x i) <=
  \big[+%R/0]_(i < m.+1) vec_norm_C (x i).
Proof.
intros. induction m.
+ rewrite !big_ord_recl //= !big_ord0. by rewrite !addr0.
+ rewrite big_ord_recr //=.
  assert (\big[+%R/0]_(i < m.+2) vec_norm_C (x i) =
           \big[+%R/0]_(i < m.+1) vec_norm_C (x (widen_ord (leqnSn m.+1) i)) +
            vec_norm_C (x ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H.
  apply /RleP.
  apply Rle_trans with
  (vec_norm_C (\big[+%R/0]_(i < m.+1) x (widen_ord (leqnSn m.+1) i)) +
   vec_norm_C (x ord_max)).
  - rewrite -RplusE. apply /RleP. apply vec_norm_add_le.
  - rewrite -!RplusE. apply Rplus_le_compat_r.
    apply /RleP. apply IHm.
Qed.


Lemma lim_norm_add:
  forall (m n:nat) (x: nat -> 'I_m.+1 -> 'cV[complex R]_n.+1),
  (forall (i: 'I_m.+1),
    is_lim_seq (fun m: nat => vec_norm_C (x m i)) 0%Re) ->
  is_lim_seq (fun p:nat => \big[+%R/0]_(i < m.+1) vec_norm_C (x p i)) 0%Re.
Proof.
intros.
induction m.
+ apply (is_lim_seq_ext (fun p : nat => vec_norm_C (x p 0)) (fun p : nat =>
              \big[+%R/0]_(i < 1) vec_norm_C (x p i))).
  - intros. by rewrite big_ord_recl //= big_ord0 //= addr0.
  - apply H.
+ apply (is_lim_seq_ext (fun p : nat =>
                                (\big[+%R/0]_(j < m.+1) (vec_norm_C (x p (widen_ord (leqnSn m.+1) j)))) + vec_norm_C (x p ord_max))
            (fun p : nat => \big[+%R/0]_(j < m.+2) (vec_norm_C (x p j)))).
  - intros. rewrite [in RHS]big_ord_recr //=.
  - assert (0%Re = (0 + 0)%Re). { nra. } rewrite H0.
    apply is_lim_seq_plus'.
    * apply IHm. intros. apply H.
    * apply H.
Qed.


Definition e_i_r {n:nat} (i: 'I_n.+1) :=
  \col_(j < n.+1) (if (i==j :> nat) then 1%Re else 0%Re).

Lemma e_i_C_e_i_r :
  forall (n:nat) (i: 'I_n.+1),
  e_i i = RtoC_vec (e_i_r i).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
by case: (i == x :> nat).
Qed.


Lemma lim_max_aux: forall (n:nat) (A: 'M[R]_n.+1),
   (forall x: 'cV[R]_n.+1,
    let vc:= RtoC_vec x in
      is_lim_seq (fun m: nat => vec_norm_C (mulmx (RtoC_mat (A^+m.+1)) vc)) 0%Re) ->
        is_lim_seq (fun m:nat => matrix_norm (RtoC_mat (A^+m.+1))) 0%Re.
Proof.
intros.
apply (is_lim_seq_le_le (fun _ => 0) (fun m : nat => matrix_norm (RtoC_mat (A ^+ m.+1)))
          (fun m:nat => \big[+%R/0]_(i < n.+1) vec_norm_C (RtoC_mat (A ^+ m.+1) *m (e_i i)))).
+ intros.
  split.
  - apply matrix_norm_ge_0.
  - unfold matrix_norm. unfold Lub_Rbar. destruct ex_lub_Rbar. simpl.
    unfold is_lub_Rbar in i. destruct i. destruct x.
    * specialize (H1 (\big[+%R/0]_(i < n.+1) vec_norm_C
                          (RtoC_mat (A ^+ n0.+1) *m  (e_i i)))).
      rewrite /Rbar_le //= in H1. apply H1.
      unfold is_ub_Rbar. intros.
      destruct H2 as [v H2]. destruct H2. rewrite H3.
      unfold Rbar_le. rewrite -RdivE.
      ++ apply Rle_trans with
          (\big[+%R/0]_(j < n.+1) (vec_norm_C (RtoC_mat (A ^+ n0.+1) *m (v j 0 *: e_i j))) / (vec_norm_C v)).
         -- rewrite -RdivE.
            + apply Rmult_le_compat_r.
              - apply Rlt_le, Rinv_0_lt_compat. apply vec_norm_gt_0.
                 unfold vec_not_zero.
                 assert (exists i, v i 0 != 0).
                 { by apply /cV0Pn. } destruct H4 as [i H4]. exists i. by apply /eqP.
              - assert (v = \big[+%R/0]_(i < n.+1) (v i 0 *: e_i i)).
                { apply base_exp. }
                assert (RtoC_mat (A ^+ n0.+1) *m v =
                        RtoC_mat (A ^+ n0.+1) *m (\big[+%R/0]_(i < n.+1) (v i 0 *: e_i i))).
                { by rewrite [in LHS]H4. } rewrite H5.
                assert (RtoC_mat (A ^+ n0.+1) *m \big[+%R/0]_(i < n.+1)
                             (v i 0 *: e_i i) =
                        \big[+%R/0]_(i < n.+1) (RtoC_mat (A ^+ n0.+1) *m (v i 0 *: e_i i))).
                { apply matrix_vec_mul_add_sum. } rewrite H6.
                apply /RleP. apply vec_norm_add_le_sum.
            + apply /eqP. apply non_zero_vec_norm.
              unfold vec_not_zero.
              assert (exists i, v i 0 != 0).
              { by apply /cV0Pn. } destruct H4 as [i H4]. exists i. by apply /eqP.
         -- rewrite -RdivE.
             * assert (\big[+%R/0]_(i < n.+1) vec_norm_C
                            (RtoC_mat (A ^+ n0.+1) *m e_i i) =
                        (((\big[+%R/0]_(i < n.+1) vec_norm_C
                            (RtoC_mat (A ^+ n0.+1) *m e_i i)) * vec_norm_C v) * /vec_norm_C v)%Re).
               { assert ((((\big[+%R/0]_(i < n.+1) vec_norm_C
                            (RtoC_mat (A ^+ n0.+1) *m e_i i)) * vec_norm_C v) * /vec_norm_C v)%Re =
                          ((\big[+%R/0]_(i < n.+1) vec_norm_C
                            (RtoC_mat (A ^+ n0.+1) *m e_i i)) * (vec_norm_C v * /vec_norm_C v))%Re).
                 { nra. } rewrite H4. rewrite Rinv_r.
                 + by rewrite Rmult_1_r.
                 + apply non_zero_vec_norm.
                    unfold vec_not_zero.
                    assert (exists i, v i 0 != 0).
                    { by apply /cV0Pn. } destruct H5 as [i H5]. exists i. by apply /eqP.
               } rewrite H4.
               apply Rmult_le_compat_r.
               ++ apply Rlt_le, Rinv_0_lt_compat,vec_norm_gt_0.
                  unfold vec_not_zero.
                  assert (exists i, v i 0 != 0).
                  { by apply /cV0Pn. } destruct H5 as [i H5]. exists i. by apply /eqP.
               ++ rewrite big_distrl //=. apply /RleP. apply big_sum_ge_ex_abstract.
                  intros. rewrite /vec_norm_C. rewrite -sqrt_mult.
                  - apply sqrt_le_1_alt. rewrite big_distrl //=.
                    apply /RleP. apply big_sum_ge_ex_abstract. intros.
                    assert (C_mod ((RtoC_mat (A ^+ n0.+1) *m (v i 0 *: e_i i)) i0 0) =
                            C_mod (v i 0 * ((RtoC_mat (A^+ n0.+1) *m e_i i) i0 0))).
                    { assert ((RtoC_mat (A ^+ n0.+1) *m (v i 0 *: e_i i)) i0 0 =
                                v i 0 * (RtoC_mat (A ^+ n0.+1) *m e_i i) i0 0).
                      { rewrite !mxE. rewrite big_distrr //=. apply eq_big.
                        by []. intros. rewrite !mxE. rewrite mulrC. rewrite -mulrA.
                        assert (((if i == i1 then (1 +i* 0)%C else (0*i)%C) *
                                      ((A ^+ n0.+1) i0 i1 +i* 0)%C) =
                                 (((A ^+ n0.+1) i0 i1 +i* 0)%C *
                                      (if i == i1 then (1 +i* 0)%C else (0*i)%C))).
                        { by rewrite mulrC. } by rewrite H8.
                      } by rewrite H7.
                    } rewrite H7. rewrite C_mod_prod. rewrite Rsqr_mult. rewrite Rmult_comm.
                    apply Rmult_le_compat_l.
                    * apply Rle_0_sqr.
                    * rewrite (bigD1 i) //=. rewrite -RplusE. apply Rsqr_le_add.
                      apply /RleP.  apply big_ge_0_ex_abstract. intros.
                      apply /RleP. apply Rle_0_sqr.
                  - apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
                  - apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
             * apply /eqP. apply non_zero_vec_norm.
               unfold vec_not_zero.
               assert (exists i, v i 0 != 0).
               { by apply /cV0Pn. } destruct H4 as [i H4]. exists i. by apply /eqP.
      ++ apply /eqP. apply non_zero_vec_norm.
         unfold vec_not_zero.
         assert (exists i, v i 0 != 0).
         { by apply /cV0Pn. } destruct H4 as [i H4]. exists i. by apply /eqP.
    * simpl. apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply vec_norm_C_ge_0.
    * simpl. apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply vec_norm_C_ge_0.
+ apply is_lim_seq_const.
+ apply lim_norm_add. intros.
  specialize (H (e_i_r i)). simpl in H.
  by rewrite e_i_C_e_i_r.
Qed.



(** If all ||S v|| / ||v|| = 0 , then it's maximum will also be 0**)
Lemma lim_max: forall (n:nat) (A: 'M[R]_n.+1) (x: 'cV[R]_n.+1),
   (forall x0: 'cV[R]_n.+1,
    let v:= x0 - x in
    let vc:= RtoC_vec v in
      is_lim_seq (fun m: nat => vec_norm_C ((RtoC_mat (A^+m.+1)) *m vc)) 0%Re) ->
        is_lim_seq (fun m:nat => matrix_norm (RtoC_mat (A^+m.+1))) 0%Re.
Proof.
intros.
apply lim_max_aux.
intros. specialize (H (x + x0)).
assert ((x + x0) - x =x0).
{ apply matrixP. unfold eqrel. intros. rewrite !mxE.
  rewrite addrC. rewrite addrA. rewrite addrC.
  assert ((- x x1 y + x x1 y)  = 0%Re).
  { rewrite addrC. rewrite -RminusE. nra. } rewrite H0.
  by rewrite addr0.
} rewrite H0 in H. apply H.
Qed.



Lemma sum_geom_gt_0: forall (x:R) (n:nat), (0<x)%Re ->
    (sum_n (fun n:nat => x^n) n >0)%Re.
Proof.
intros.
induction n.
+ assert (sum_n (fun n : nat => (x ^ n)%Re) 0%N = (fun n : nat => (x ^ n)%Re) 0%N).
  { apply sum_n_n. } rewrite H0. simpl. nra.
+ assert (sum_n (fun n0 : nat => (x ^ n0)%Re) (S n) =
            (sum_n (fun n : nat => (x ^ n)%Re) n + x^ (S n))%Re).
  { apply (sum_Sn (fun n0 : nat => (x ^ n0)%Re) n). } rewrite H0.
  apply Rplus_lt_0_compat. apply IHn.
  apply pow_lt. apply H.
Qed.


Lemma powr_decr: forall (x:R) (n:nat),
  (0<=x)%Re -> (x^n < 1)%Re -> (x < 1)%Re.
Proof.
intros.
assert (x= 0%Re \/ (0<x)%Re). { nra. } destruct H1.
+ rewrite H1. apply Rlt_0_1.
+ assert ( (x^n <1)%Re -> (x^n -1 < 0)%Re). { nra. }
  specialize (H2 H0).
  assert ( (0<=n)%N ). { apply leq0n. }
  assert ( (0==n)%N \/ (0<n)%N). { apply /orP. by rewrite -leq_eqVlt. }
  destruct H4.
  - assert (n= 0%N). { apply /eqP. by rewrite eq_sym. }
    rewrite H5 in H0. simpl in H0. contradict H0. nra.
  -  assert ( (x^n - 1)%Re = ((sum_f_R0 (fun n:nat => (x^n)) (n.-1))* (x-1))%Re).
    { symmetry.  assert (((n.-1)+1)%N = n). {  rewrite addn1. by apply prednK. }
      assert ((x ^ n - 1)%Re = (x^ (((n.-1)+1)%nat)-1)%Re).
      { rewrite H5. nra. } rewrite H6. apply GP_finite.
    } rewrite H5 in H2.
    assert ( (x-1<0)%Re -> (x<1)%Re). { nra. } apply H6.
    apply Rmult_lt_reg_l with
          (sum_f_R0 (fun n : nat => x ^ n) (n.-1))%Re.
    assert ((sum_n (fun n0 : nat => x ^ n0) (n.-1))%Re =
              (sum_f_R0 (fun n0 : nat => x ^ n0) (n.-1))%Re).
    { apply sum_n_Reals. } rewrite <- H7.
    apply sum_geom_gt_0. nra.
    intros. nra.
Qed.

(** \lim_{m \to \infty} q^n = 0 --> |q| < 1 **)
Lemma is_lim_seq_geom_nec (q:R):
  is_lim_seq (fun n => (q ^ n.+1)%Re) 0%Re -> Rabs q <1.
Proof.
intros.
assert (is_lim_seq' (fun n : nat => (q ^ n.+1)%Re) 0%Re <-> is_lim_seq (fun n : nat => (q ^ n.+1)%Re) 0%Re).
{ apply is_lim_seq_spec. }
destruct H0. specialize (H1 H). clear H0.
unfold is_lim_seq' in H1.
assert ((1>0)%Re). { nra. }
specialize (H1 (mkposreal 1 H0)).
unfold eventually in H1. destruct H1 as [N H1].
specialize (H1 N). assert ((N <= N)%coq_nat). { lia. }
specialize (H1 H2).
assert ((q ^ N.+1 - 0)%Re = (q^N.+1)%Re). { nra. }  rewrite RminusE in H1.
rewrite RminusE in H3. rewrite RpowE in H3. rewrite RpowE in H1. rewrite H3 in H1. clear H2 H3.
apply /RltbP. simpl in H1.  clear H H0.
assert (Rabs (q ^+N.+1) = (Rabs q)^+N.+1). { symmetry. rewrite -!RpowE. apply RPow_abs. }
rewrite H in H1. clear H.
apply (@powr_decr (Rabs q) N.+1). apply Rabs_pos. rewrite RpowE. apply H1.
Qed.


(** Av = \lambda v --> A^m v = \lambda^m v **)
Lemma eigen_power: forall (n m:nat) (i: 'I_n.+1) (A: 'M[R]_n.+1) (v: 'cV_n.+1),
  let Ap:= RtoC_mat A in
  mulmx Ap v = scal_vec_C (lambda Ap i) v ->
  RtoC_mat (A^+m) *m v = scal_vec_C (lambda Ap i ^+ m) v.
Proof.
intros.
induction m.
+ by rewrite //= !expr0 -scal_vec_1 RtoC_Mone mul1mx.
+ simpl.
  assert (RtoC_mat (mulmx (A^+m) A) =
            mulmx (RtoC_mat (A^+m)) (RtoC_mat A)).
  { by rewrite -RtoC_mat_prod. }
  rewrite exprSr exprS H0.
  assert (scal_vec_C (lambda Ap i)
            (scal_vec_C (lambda Ap i ^+ m) v) =
          scal_vec_C (lambda Ap i * lambda Ap i ^+ m) v).
  { apply scal_of_scal_vec. } rewrite -H1.
  rewrite -IHm. rewrite scale_vec_mat_conv_C.
  rewrite -mulmxA. by rewrite H.
Qed.



Lemma mat_power_R_C_compat: forall (m n: nat) (A: 'M[R]_n.+1),
  let Ap:= RtoC_mat A in RtoC_mat (A^+m) = Ap^+m.
Proof.
intros. unfold Ap.
induction m.
+ by rewrite !expr0 RtoC_Mone.
+ by rewrite !exprS -RtoC_mat_prod IHm.
Qed.

Lemma Mopp_add_left: forall (m n:nat) (A B C: 'M[R]_(m,n)),
  A = addmx B C -> addmx A (oppmx B) = C.
Proof.
intros. by rewrite H addmxC addmxA Mplus_opp_l Mplus_0_l.
Qed.

Lemma Mopp_add_right: forall (m n:nat) (A B C: 'M[R]_(m,n)),
  addmx A B = C -> A = addmx (oppmx B) C.
Proof.
intros. by rewrite -H addmxC -addmxA Mplus_opp_r Mplus_0_r.
Qed.

Lemma big_ge_0_ex:
  forall (n : nat)  (x: 'I_n.+1 -> R) (i: 'I_n.+1) ,
  (0 <= \big[+%R/0]_(i0 < n.+1 | i0 != i) (x i0)²)%Re.
Proof.
intros. apply /RleP.
apply big_ge_0_ex_abstract.
intros. apply /RleP. apply Rle_0_sqr.
Qed.

(** If x i <> 0 --> \sum_i (x i ) > 0 **)
Lemma big_gt_0_ex:
  forall (n : nat) (x: 'I_n.+1 -> R),
    (exists i : 'I_n.+1, x i <> 0%Re )->
    (0 < (\big[+%R/0]_l (x l)²))%Re.
Proof.
intros. destruct H as [i H]. rewrite (bigD1 i) //=.
rewrite -RplusE.
apply Rplus_lt_le_0_compat.
+ by apply Rsqr_pos_lt.
+ by apply big_ge_0_ex.
Qed.

(** (x i) <> 0 --> ||x|| <> 0 **)
Lemma vec_norm_not_zero: forall (n : nat) (x: 'cV[R]_n.+1),
  (exists i:'I_n.+1, x i 0  <> 0%Re) ->
  vec_norm x <> 0%Re.
Proof.
intros.
assert ( (0< vec_norm x)%Re -> vec_norm x <> 0%Re).
{ nra. } apply H0. rewrite /vec_norm. apply sqrt_lt_R0.
by apply big_gt_0_ex.
Qed.

Lemma Mopp_add_compat:
  forall (n:nat) (A: 'M[R]_n.+1) (X b: 'cV[R]_n.+1),
  addmx (oppmx (A *m X) + b) (A *m X) = b.
Proof.
intros. apply matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite addrC. rewrite addrA.
rewrite addrC.
assert ((\big[+%R/0]_j (A x j * X j y) -
              \big[+%R/0]_j (A x j * X j y)) = 0).
{ apply /eqP. by rewrite subr_eq0. } by rewrite H addr0.
Qed.


Lemma vec_norm_0 {n:nat} : vec_norm (0 : 'M[R]_(n.+1,1)) = 0.
Proof.
rewrite /vec_norm.
assert (\big[+%R/0]_l (Rsqr ((0 : 'M[R]_(n.+1,1)) l 0))  = 0).
{ rewrite -[RHS](big_0_sum n). apply eq_big. by [].
  intros. rewrite mxE. by rewrite Rsqr_0.
} rewrite H. by rewrite sqrt_0.
Qed.

(** State the iterative convergence theorem **)
Theorem iter_convergence:
  forall (n:nat) (A: 'M[R]_n.+1) (b: 'cV[R]_n.+1)
  (A1 A2 : 'M[R]_n.+1),
  A \in unitmx ->
   A1 \in unitmx ->
   A = A1 + A2 ->
   let x := (invmx A) *m b in
   (let S_mat:= RtoC_mat (- ( A1^-1 *m A2)) in
     (forall (i: 'I_n.+1), (C_mod (lambda S_mat i) < 1)%Re)) <->
    (forall x0: 'cV[R]_n.+1,
        is_lim_seq (fun m:nat => vec_norm ((X_m m.+1 x0 b A1 A2) - x)) 0%Re).
Proof.
intros.
assert (A *m x = b).
{ assert (b = 1%:M *m b). { by rewrite mul1mx. }
  rewrite H2.
  assert (A *m (invmx A) = 1%:M). { by apply inverse_A. }
  rewrite -H3. rewrite /x.  by rewrite -mulmxA.
}

assert (forall (n:nat) (A: 'M[complex R]_n.+1) (i: 'I_n.+1),
            @eigenvalue (complex_fieldType _) n.+1 A (lambda A i)).
{ apply Jordan_ii_is_eigen. }
assert (forall x0: 'cV[R]_n.+1,
         is_lim_seq (fun m:nat => vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx x)))
              (vec_norm (addmx (X_m 0 x0 b A1 A2) (oppmx x)))).
{ intros. apply is_lim_seq_const. }

assert (forall (x0: 'cV[R]_n.+1) (m:nat),
          addmx (mulmx A1 (X_m m.+1 x0 b A1 A2)) (mulmx A2 (X_m m x0 b A1 A2)) =b).
{ intros. simpl.
  rewrite -Mopp_mult_l.
  rewrite Mopp_mult_r. rewrite -mulmxA. rewrite mulmxDr.
  rewrite !mulmxA.
  assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
  rewrite H5. rewrite !mul1mx. rewrite -Mopp_mult_r.
  apply (@Mopp_add_compat n A2 (X_m m x0 b A1 A2) b).
}

assert (forall (x0 : 'cV[R]_n.+1) (m : nat),
          vec_norm
            (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1)
               (addmx (X_m 0 x0 b A1 A2) (oppmx x))) =
          vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx x))).
{ intros. apply vec_norm_eq. symmetry.
  induction m.
  + rewrite expr1. rewrite -[LHS]mul1mx [in RHS]Mopp_mult_r.
    assert (mulmx (invmx A1) A1 = 1%:M). { by apply inverse_A. }
    rewrite -H6 -!mulmxA.
    assert ( (A1 *m addmx (X_m 1 x0 b A1 A2) (oppmx x)) =
              (oppmx A2 *m addmx (X_m 0 x0 b A1 A2) (oppmx x))).
    { rewrite !mulmxDr.
      assert (A1 *m (oppmx (invmx A1 *m A2) *m x0) =
                  oppmx A2 *m X_m 0 x0 b A1 A2).
      { rewrite mulmxA. rewrite Mopp_mult_l. rewrite mulmxA.
        rewrite -Mopp_mult_r.
        assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
        rewrite H7 //=. clear H7. rewrite -mulmxA.
        by rewrite -!Mopp_mult_l mul1mx.
      } rewrite H7.
      rewrite mulmxA.
      assert (A1 *m invmx A1 = 1%:M). { by apply inverse_A. }
      rewrite H8. rewrite mul1mx.
      rewrite -H2.
      assert (A *m x + A1 *m oppmx x = oppmx A2 *m oppmx x).
      { rewrite -!Mopp_mult_r. rewrite Mopp_mult_l -mulmxDl.
        rewrite -Mopp_mult_l. rewrite Mopp_opp.
        rewrite H1. rewrite addrC addrA. rewrite addrC.
        assert ((oppmx A1 + A1) = 0).
        { apply matrixP. unfold eqrel. intros. rewrite !mxE. apply addNr. }
        rewrite H9. by rewrite addr0.
      } rewrite -addrA. by rewrite H9.
    } by rewrite H7.
  + rewrite exprS. specialize (H5 x0 (m.+1)).
    rewrite -mulmxA -IHm.
    assert (mulmx (oppmx (mulmx (invmx A1) A2)) (addmx (X_m m.+1 x0 b A1 A2) (oppmx x))=
            addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
                  (mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx x))).
    { apply mulmxDr. } rewrite H6.
    assert ((mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx x))=
              mulmx (mulmx (invmx A1) A2) x).
    { assert (mulmx (oppmx (mulmx (invmx A1) A2)) (oppmx x)=
                oppmx (mulmx (oppmx (mulmx (invmx A1) A2)) x)).
      { symmetry. apply Mopp_mult_r. } rewrite H7.
      assert (mulmx (oppmx (mulmx (invmx A1) A2)) x =
                oppmx (mulmx (mulmx (invmx A1) A2) x)).
      { symmetry. apply Mopp_mult_l. } rewrite H8.
      apply Mopp_opp.
    } rewrite H7.
    assert ((mulmx (mulmx (invmx A1) A2) x) =
                addmx (mulmx (invmx A1) b) (oppmx x)).
    { assert (addmx (mulmx (invmx A1) b) (oppmx x) = addmx
                (oppmx x) (mulmx (invmx A1) b)). { apply addmxC. }
      rewrite H8.
      assert (mulmx A x = b). { apply H2. } rewrite <-H9. clear H9.
      assert (mulmx A x = mulmx (addmx A1 A2) x).
      { assert (addmx A1 A2 = A1 + A2). { by []. } by rewrite H9 -H1. } rewrite H9.
      assert (mulmx (addmx A1 A2) x = addmx (mulmx A1 x) (mulmx A2 x)).
      { apply mulmxDl. } rewrite H10.
      assert (mulmx (invmx A1)
                (addmx (mulmx A1 x) (mulmx A2 x)) =
               addmx (mulmx (invmx A1) (mulmx A1 x))
                  (mulmx (invmx A1) (mulmx A2 x))).
      { apply mulmxDr. } rewrite H11.
      assert ((mulmx (invmx A1) (mulmx A1 x)) =
                mulmx (mulmx (invmx A1) A1) x). { apply mulmxA. }
      rewrite H12.
      assert (mulmx (invmx A1) A1 = 1%:M). { by apply inverse_A. }
      rewrite H13.
      assert (mulmx 1%:M x = x). { apply mul1mx. } rewrite H14.
      assert (mulmx (mulmx (invmx A1) A2) x = addmx 0
                (mulmx (mulmx (invmx A1) A2) x)).
      { symmetry.
        assert (addmx 0 (mulmx (mulmx (invmx A1) A2) x)=
                   addmx (mulmx (mulmx (invmx A1) A2) x) 0).
        { apply addmxC. } rewrite H15. apply Mplus_0_r.
      } rewrite H15.
      assert (0= addmx (oppmx x) x).
      { assert (addmx (oppmx x) x = addmx x (oppmx x)).
        { apply addmxC. } rewrite H16. symmetry. apply Mplus_opp_r.
      } rewrite H16.
      symmetry.
      assert ((mulmx (invmx A1) (mulmx A2 x)) =
                (mulmx (mulmx (invmx A1) A2) x)).
      { apply mulmxA. } rewrite H17. apply addmxA.
    }
    rewrite H8.
    assert (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
              (addmx (mulmx (invmx A1) b) (oppmx x))=
            addmx (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
                        (mulmx (invmx A1) b)) (oppmx x)).
    { apply addmxA. } rewrite H9.
    assert (X_m m.+2 x0 b A1 A2 =
              (addmx (mulmx (oppmx (mulmx (invmx A1) A2)) (X_m m.+1 x0 b A1 A2))
                  (mulmx (invmx A1) b))).
    { assert (oppmx (mulmx (invmx A1) A2) = mulmx (invmx A1) (oppmx A2)).
      { apply Mopp_mult_r. } rewrite H10.
      assert (mulmx (mulmx (invmx A1) (oppmx A2)) (X_m m.+1 x0 b A1 A2)=
                  mulmx (invmx A1) (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2))).
      { symmetry. apply mulmxA. } rewrite H11.
      assert (mulmx (invmx A1) (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b)=
                addmx (mulmx (invmx A1) (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)))
                  (mulmx (invmx A1) b)).
      { apply mulmxDr. } rewrite <-H12.
      assert (X_m m.+2 x0 b A1 A2 = mulmx 1%:M (X_m m.+2 x0 b A1 A2)).
      { symmetry. apply mul1mx. }
      rewrite H13.
      assert (mulmx (invmx A1) A1 = 1%:M). {  by apply inverse_A. } rewrite -H14.
      assert (mulmx (mulmx (invmx A1) A1) (X_m m.+2 x0 b A1 A2) =
                mulmx (invmx A1) (mulmx A1 (X_m m.+2 x0 b A1 A2))).
      { symmetry. apply mulmxA. } rewrite H15.
      assert (mulmx A1 (X_m m.+2 x0 b A1 A2) = (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b)).
      { assert (addmx (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2)) b = addmx b (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2))).
       { apply addmxC. } rewrite H16.
       assert (mulmx (oppmx A2) (X_m m.+1 x0 b A1 A2) = oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))).
       { symmetry. apply Mopp_mult_l. } rewrite H17.
       assert (mulmx A1 (X_m m.+2 x0 b A1 A2) = addmx (mulmx A1 (X_m m.+2 x0 b A1 A2)) 0).
       { symmetry. apply Mplus_0_r. } rewrite H18.
       assert (addmx (mulmx A2 (X_m m.+1 x0 b A1 A2)) (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))) = 0).
       { apply Mplus_opp_r. } rewrite <-H19.
       assert (addmx (mulmx A1 (X_m m.+2 x0 b A1 A2))
                  (addmx (mulmx A2 (X_m m.+1 x0 b A1 A2)) (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2))))=
                addmx (addmx (mulmx A1 (X_m m.+2 x0 b A1 A2)) (mulmx A2 (X_m m.+1 x0 b A1 A2)))
                    (oppmx (mulmx A2 (X_m m.+1 x0 b A1 A2)))).
       { apply addmxA. } rewrite H20.
       by rewrite H5.
     } by rewrite H16.
    } by rewrite H10.
}

(** Splitting things here **)
assert ((forall x0: 'cV[R]_n.+1,
          is_lim_seq (fun m : nat => vec_norm  ((X_m m.+1 x0 b A1 A2) - x)) 0%Re) <->
        is_lim_seq (fun m:nat =>  (matrix_norm
              (RtoC_mat ((- (A1^-1 *m A2))^+m.+1) ))) 0%Re).
{ split.
  + intros.
    apply lim_max with x. intros.
    specialize (H7 x0).
    apply (is_lim_seq_ext
            (fun m : nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx x)))
            (fun m : nat => vec_norm_C
                (RtoC_mat (oppmx (invmx A1 *m A2) ^+ m.+1) *m vc))).
    - intros. specialize (H6 x0 n0).
      rewrite -H6. rewrite -mat_vec_unfold. rewrite vec_norm_R_C.
      simpl. by rewrite /v.
    - apply H7.
  + intros.
    assert ((x0 - x) = 0 \/ (x0 - x) != 0).
    { assert (RtoC_vec (x0 - x) = 0 \/ RtoC_vec (x0 - x) != 0).
      { apply vec_is_zero_or_not. } destruct H8.
      + left.
        apply matrixP. unfold eqrel. intros. rewrite [RHS]mxE.
        apply matrixP in H8. unfold eqrel in H8.
        specialize (H8 x1 y). rewrite mxE in H8.
        assert (((x0 - x) x1 0 +i* 0)%C == (0: 'M[complex R]_(n.+1,1)) x1 y).
        { by apply /eqP. } rewrite eq_complex in H9.
        simpl in H9.
        assert (((x0 - x) x1 0 == Re ((0: 'M[complex R]_(n.+1,1)) x1 y)) /\
                   (0 == Im ((0: 'M[complex R]_(n.+1,1)) x1 y))).
        { by apply /andP. } destruct H10.
        assert ((x0 - x) x1 0 = Re ((0: 'M[complex R]_(n.+1,1)) x1 y)).
        { by apply /eqP. }
        assert (y = 0). { by apply ord1. } rewrite H13. rewrite H12.
        by rewrite mxE.
      + right. apply /cV0Pn.
        assert (exists i, RtoC_vec (x0 - x) i 0 != 0).
        { by apply /cV0Pn. } destruct H9 as [i H9]. exists i.
        rewrite eq_complex in H9.
        assert (~~ (Re (RtoC_vec (x0 - x) i 0) == Re 0) \/
                ~~(Im (RtoC_vec (x0 - x) i 0) == Im 0)).
        { by apply /nandP. } destruct H10.
        - rewrite mxE //= in H10.
        - rewrite mxE //= in H10.
          assert ( 0%Re <> 0%Re). { by apply /eqP. } by contradict H11.
      } destruct H8.
    - apply (is_lim_seq_ext (fun m:nat => vec_norm (mulmx ((oppmx
                (mulmx (invmx A1) A2))^+m.+1) (addmx (X_m 0 x0 b A1 A2) (oppmx x))))
              (fun m : nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx x)))).
      * apply H6.
      * apply (is_lim_seq_ext (fun _ => 0)
                  (fun m : nat =>
                     vec_norm
                       (oppmx (invmx A1 *m A2) ^+ m.+1 *m
                        addmx (X_m 0 x0 b A1 A2) (oppmx x)))).
        ++ intros. rewrite //=.
           assert (addmx x0 (oppmx x) = 0).
           { apply matrixP. unfold eqrel. intros. rewrite [RHS]mxE.
             assert ([forall i, forall j, (x0 - x) i j == 0]).
             { rewrite -matrix_eq0. by apply /eqP. }
             assert (forall i, [forall j,  (x0 - x) i j == 0]).
             { by apply /forallP. }
             specialize (H10 x1).
             assert (forall j, (x0 - x) x1 j == 0).
             { by apply /forallP. } specialize (H11 y).
             apply /eqP. apply H11.
           } rewrite H9. rewrite mulmx0.
           by rewrite vec_norm_0.
        ++ by apply is_lim_seq_const.
    - apply (is_lim_seq_ext (fun m:nat => vec_norm (mulmx ((oppmx
                (mulmx (invmx A1) A2))^+m.+1) (addmx (X_m 0 x0 b A1 A2) (oppmx x))))
              (fun m : nat => vec_norm (addmx (X_m m.+1 x0 b A1 A2) (oppmx x)))).
      * apply H6.
      * apply (is_lim_seq_ext (fun m : nat =>
                 vec_norm_C
                   (RtoC_vec (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1 )
                      (addmx (X_m 0 x0 b A1 A2) (oppmx x))))) (fun m : nat =>
                 vec_norm
                   (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1 )
                      (addmx (X_m 0 x0 b A1 A2) (oppmx x)))) 0%Re).
        intros.
        apply vec_norm_R_C.
        apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
                   vec_norm_C
                     (RtoC_vec
                        (mulmx ((oppmx (mulmx (invmx A1) A2))^+m.+1)
                           (addmx (X_m 0 x0 b A1 A2) (oppmx x)))))  (fun m : nat =>
                  (matrix_norm
                    (RtoC_mat
                       ((oppmx (mulmx (invmx A1) A2))^+m.+1 ))) *
                    (vec_norm_C (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx x)))))%Re 0%Re).
        ++ intros. split.
          apply vec_norm_C_ge_0.
          assert ( RtoC_vec
                   (mulmx ((oppmx (mulmx (invmx A1) A2))^+n0.+1)
                      (addmx (X_m 0 x0 b A1 A2) (oppmx x))) = mulmx
                    (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+n0.+1 ))
                    (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx x)))).
          { apply mat_vec_unfold. } rewrite H9.
          apply /RleP. apply matrix_norm_compat.
          rewrite //=.
          assert ((exists i: 'I_n.+1, addmx x0 (oppmx x) i 0 != 0)).
          {by  apply /cV0Pn. }
          apply /cV0Pn. destruct H10 as [k H10]. exists k. rewrite mxE.
          rewrite eq_complex. apply /nandP. left. by rewrite //=.
        ++ apply is_lim_seq_const.
          assert ( 0%Re = (0* vec_norm_C (RtoC_vec (addmx (X_m 0 x0 b A1 A2) (oppmx x))))%Re).
          { nra. } rewrite H9.
          apply is_lim_seq_mult'.
          { apply H7. }
          apply is_lim_seq_const.
}

assert (is_lim_seq (fun m:nat => matrix_norm
          (RtoC_mat ((- ((A1^-1 *m A2)))^+m.+1 ))) 0%Re <->
        (let S_mat :=
           RtoC_mat (- (A1^-1 *m A2)) in
         forall i : 'I_n.+1,
         (C_mod (lambda S_mat i) < 1)%Re)).
{ split.

  + intros.
    assert (Rabs (C_mod (lambda S_mat i))= C_mod (lambda S_mat i)).
    { apply Rabs_right. apply Rle_ge. apply C_mod_ge_0. } rewrite <-H9.
    apply /RltP. apply (@is_lim_seq_geom_nec (C_mod (lambda S_mat i))).
    specialize (H3 _ S_mat i).  apply right_eigen_vector_exists in H3.
    destruct H3 as [v H3].
    apply (is_lim_seq_ext  (fun n0 : nat => ((C_mod (lambda S_mat i) ^ n0.+1)*
              ((vec_norm_C  v) / (vec_norm_C v)))%Re)
              (fun n0 : nat => (C_mod (lambda S_mat i) ^ n0.+1)%Re)).
    intros.
    assert ((vec_norm_C v / vec_norm_C v)%Re = 1).
    {  apply Rinv_r. apply non_zero_vec_norm. destruct H3.
       unfold vec_not_zero.
       assert (exists i, v i 0 != 0).
       { by apply /cV0Pn. } destruct H11 as [j H11]. exists j. by apply /eqP.
    } rewrite H10.
    rewrite RmultE. by rewrite mulr1.
    apply (is_lim_seq_ext (fun n0 : nat =>
             ((C_mod (lambda S_mat i) ^ n0.+1 *
              vec_norm_C v) / vec_norm_C v)%Re)).
    intros. nra.
    assert (0%Re = (0/ vec_norm_C v)%Re). { nra. } rewrite H10.
    apply is_lim_seq_div'.

    apply (is_lim_seq_ext (fun m:nat => vec_norm_C
                  (scal_vec_C ((lambda S_mat i)^m.+1) v)) (fun n0 : nat =>
                  (C_mod (lambda S_mat i) ^ n0.+1 * vec_norm_C v)%Re)).
    intros.
    assert (((C_mod (lambda S_mat i))^n0.+1)%Re = C_mod ((lambda S_mat i)^n0.+1)).
    { by rewrite RpowE C_mod_pow. }
    rewrite H11. apply ei_vec_ei_compat.
    apply (is_lim_seq_ext (fun m:nat => vec_norm_C (mulmx
              (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^+m.+1)) v))
              (fun m : nat =>
                 vec_norm_C
                   (scal_vec_C ((lambda S_mat i)^+m.+1) v))).
    intros.
    assert (mulmx
               (RtoC_mat
                  ((oppmx (mulmx (invmx A1) A2))^+n0.+1 )) v
                = scal_vec_C ((lambda S_mat i)^+n0.+1) v).
    { unfold S_mat. apply eigen_power. fold S_mat.
      rewrite -scal_vec_mathcomp_compat_col. apply H3.
    }
    rewrite H11. reflexivity.
    apply (is_lim_seq_le_le (fun m:nat => 0%Re) (fun m : nat =>
             vec_norm_C
               (mulmx
                  (RtoC_mat
                     ((oppmx (mulmx (invmx A1) A2))^m.+1)) v)) (fun m:nat => ((matrix_norm
                (RtoC_mat
                   ((oppmx (mulmx (invmx A1) A2))^m.+1 ))) *
                vec_norm_C v)%Re)).
    intros.
    split.
    + apply vec_norm_C_ge_0.
    + apply /RleP. apply matrix_norm_compat.
      by apply H3.
    apply is_lim_seq_const.
    assert (0%Re = (0* vec_norm_C v)%Re).
    { nra. } rewrite H11.
    apply is_lim_seq_mult'.
    apply H8. apply is_lim_seq_const.
    apply is_lim_seq_const. apply non_zero_vec_norm. destruct H3.
    unfold vec_not_zero.
    assert (exists i, v i 0 != 0).
    { by apply /cV0Pn. } destruct H12 as [j H12]. exists j . by apply /eqP. by [].

  + intros.

    apply (is_lim_seq_ext (fun m : nat =>
                   matrix_norm
                     ((RtoC_mat (oppmx (mulmx (invmx A1) A2)))^+m.+1 ))

                (fun m : nat =>
                   matrix_norm
                     (RtoC_mat
                        ((oppmx (mulmx (invmx A1) A2))^+m.+1)))).
    intros.
    assert (RtoC_mat
                ((oppmx (mulmx (invmx A1) A2))^+n0.+1) =
                  (RtoC_mat (oppmx (mulmx (invmx A1) A2)))^+n0.+1).
    { apply mat_power_R_C_compat. } by rewrite H9.
    by apply mat_norm_converges.
}

apply iff_trans with (is_lim_seq
       (fun m : nat =>
        matrix_norm
          (RtoC_mat ((oppmx (mulmx (invmx A1) A2))^m.+1))) 0%Re).
+ symmetry. apply H8.
+ symmetry. apply H7.
Qed.

