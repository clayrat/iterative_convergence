Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop.
From mathcomp.analysis Require Import boolp Rstruct classical_sets signed
     topology normedtype landau sequences.
Require Import Coquelicot.Lim_seq.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Hierarchy Coquelicot.Lub.
From mathcomp Require Import mxalgebra matrix all_field.
From CoqEAL Require Import mxstructure ssrcomplements jordan similar closed_poly frobenius_form.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Open Scope classical_set_scope.

From mathcomp Require Import complex.
Import ComplexField.
Require Import complex_mat_vec_prop.


(** Define 2 -norm of a matrix **)
Definition matrix_norm (n:nat) (A: 'M[complex R]_n.+1) :=
    Lub_Rbar (fun x=>
      exists v: 'cV[complex R]_n.+1, v != 0 /\
                x = (vec_norm_C  (mulmx A v))/ (vec_norm_C v)).

(** Define the Frobenius matrix norm **)
Definition mat_norm (n:nat) (A: 'M[complex R]_n.+1) : R:=
  sqrt (\sum_i (\sum_j (Rsqr (C_mod (A i j))))).

Definition one_vec (n:nat) : 'cV[complex R]_n.+1:=
  \col_(j < n.+1) (if (j == 0%N :> nat) then (1 +i* 0)%C else (0 +i* 0)%C).

Lemma one_vec_norm_1 (n:nat):
  vec_norm_C (one_vec n) = 1%Re.
Proof.
intros. rewrite /vec_norm_C.
assert ((0<=n)%N). { by []. } rewrite leq_eqVlt in H.
assert (n= 0%N \/ (0<n)%N).
{ assert ((0%N == n) \/ (0 < n)%N). { by apply /orP. }
  destruct H0.
  + left. rewrite eq_sym in H0. by apply /eqP.
  + by right.
} destruct H0.
+ rewrite H0. rewrite big_ord_recl //= big_ord0.
  rewrite addr0 !mxE //= /C_mod //=.
  rewrite !expr2 mulr0 mulr1 Rplus_0_r sqrt_1.
  rewrite sqrt_Rsqr; nra.
+ rewrite big_ord_recl //=. rewrite -RplusE.
  assert (\big[+%R/0]_(i < n) (C_mod
                            (one_vec n (lift ord0 i) 0))² = 0%Re).
  { rewrite -(big_0_sum n.-1).
    assert (n.-1.+1 = n). { by rewrite prednK. }
    rewrite H1. apply eq_big. by [].
    intros. rewrite !mxE //=. rewrite /C_mod //=.
    rewrite expr2 !mulr0 Rplus_0_r sqrt_0//= /Rsqr. nra.
  } rewrite H1. rewrite Rplus_0_r. rewrite !mxE /C_mod //=.
  rewrite !expr2 mulr0 mulr1 Rplus_0_r sqrt_1.
  rewrite sqrt_Rsqr; nra.
Qed.

Lemma big_0_sum_0: forall (n:nat),
  \big[+%R/0]_(j<n) 0 = 0 :>complex R.
Proof.
intros. induction n.
+ by rewrite big_ord0.
+ rewrite big_ord_recr //=. rewrite IHn. apply add0r.
Qed.

Lemma matrix_norm_ge_0_aux :
  forall (n:nat) (A: 'M[complex R]_n.+1),
  Rbar_le 0%Re (matrix_norm A).
Proof.
intros.
apply Rbar_le_trans with (sqrt (\big[+%R/0]_i (Rsqr (C_mod (A i 0))))).
+ rewrite /Rbar_le. apply sqrt_pos.
+ rewrite /matrix_norm.
  rewrite /Lub_Rbar. destruct ex_lub_Rbar.
  simpl. rewrite /is_lub_Rbar in i.
  destruct i. unfold is_ub_Rbar in H.
  specialize (H (sqrt (\big[+%R/0]_i (Rsqr (C_mod (A i 0)))))).
  unfold Rbar_le in H. apply H. intros.
  exists (one_vec n). split.
  + apply /cV0Pn. exists 0. rewrite mxE //=. by rewrite oner_neq0.
    (*rewrite one_vec_norm_1.
      assert ((0<1)%Re -> 1%Re <> 0%Re). { nra. } apply H1. nra. *)
  + rewrite one_vec_norm_1. rewrite divr1.
    rewrite /vec_norm_C.
    assert (\big[+%R/0]_i (C_mod (A i 0))² =
            \big[+%R/0]_l (C_mod ((A *m one_vec n) l 0))²).
    { apply eq_big. by []. intros.
      rewrite !mxE.
      rewrite big_ord_recl //=. rewrite !mxE //=.
      assert (\big[+%R/0]_(i0 < n) (A i (lift ord0 i0) *
                          one_vec n (lift ord0 i0) 0) = 0:> complex R).
      { rewrite -[RHS](big_0_sum_0 n). apply eq_big. by [].
        intros. rewrite !mxE //=. by rewrite mulr0.
      } rewrite H2 addr0 //=. by simpc.
    } by rewrite H1.
Qed.

Lemma vec_norm_gt_0: forall (n:nat) (v: 'cV[complex R]_n.+1),
  vec_not_zero v -> (0 < vec_norm_C v)%Re.
Proof.
intros.
unfold vec_not_zero in H.
unfold vec_norm_C.
apply sqrt_lt_R0. destruct H as [i H].
rewrite (bigD1 i) //=.
rewrite -RplusE.
apply Rplus_lt_le_0_compat.
+ assert (0%Re = Rsqr 0). { by rewrite Rsqr_0. }
  rewrite H0. apply Rsqr_incrst_1.
  - apply /RltP. by apply C_mod_gt_0.
  - nra.
  - apply C_mod_ge_0.
+ apply /RleP. apply big_ge_0_ex_abstract.
  intros. apply /RleP. apply Rle_0_sqr.
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


Lemma sum_prod_le: forall (n:nat) (u v : 'I_n.+1 -> R),
  (forall j:'I_n.+1, 0 <= u j) ->
  (forall j: 'I_n.+1, 0 <= v j) ->
  \big[+%R/0]_j (u j * v j) <=
  (\big[+%R/0]_j u j * \big[+%R/0]_j v j).
Proof.
intros. induction n.
+ simpl. by rewrite !big_ord_recr //= !big_ord0 !add0r.
+ simpl. rewrite big_ord_recr //=.
  assert (\big[+%R/0]_(j < n.+2) u j =
            \big[+%R/0]_(j < n.+1) (u (widen_ord (leqnSn n.+1) j)) +
            u ord_max).
  { by rewrite big_ord_recr //=. } rewrite H1.
  assert (\big[+%R/0]_(j < n.+2) v j =
            \big[+%R/0]_(j < n.+1) (v (widen_ord (leqnSn n.+1) j)) +
            v ord_max).
  { by rewrite big_ord_recr //=. } rewrite H2.
  clear H1 H2. rewrite !mulrDr !mulrDl.
  apply /RleP. rewrite -!RplusE -!RmultE.
  assert ((\big[+%R/0]_(j < n.+1) u (widen_ord (leqnSn n.+1) j) *
             \big[+%R/0]_(j < n.+1) v (widen_ord (leqnSn n.+1) j) +
             u ord_max *
             \big[+%R/0]_(j < n.+1) v (widen_ord (leqnSn n.+1) j) +
             (\big[+%R/0]_(j < n.+1) u (widen_ord (leqnSn n.+1) j) *
              v ord_max + u ord_max * v ord_max))%Re =
          (\big[+%R/0]_(j < n.+1) u (widen_ord (leqnSn n.+1) j) *
             \big[+%R/0]_(j < n.+1) v (widen_ord (leqnSn n.+1) j) +
            ((u ord_max * v ord_max) +
             (u ord_max *
             \big[+%R/0]_(j < n.+1) v (widen_ord (leqnSn n.+1) j) +
             (\big[+%R/0]_(j < n.+1) u (widen_ord (leqnSn n.+1) j) *
              v ord_max ))))%Re).
  { nra. } rewrite H1. clear H1. apply Rplus_le_compat.
  - apply /RleP. rewrite RmultE. apply IHn.
    * intros. apply H.
    * intros. apply H0.
  - assert ((u ord_max * v ord_max)%Re = (u ord_max * v ord_max + 0)%Re).
    { nra. } rewrite H1.
    assert ((u ord_max * v ord_max + 0 +
               (u ord_max *
                \big[+%R/0]_(j < n.+1) v (widen_ord (leqnSn n.+1) j) +
                \big[+%R/0]_(j < n.+1) u (widen_ord (leqnSn n.+1) j) *
                v ord_max))%Re =
            ((u ord_max * v ord_max) +
             (u ord_max *
             \big[+%R/0]_(j < n.+1) v (widen_ord (leqnSn n.+1) j) +
             (\big[+%R/0]_(j < n.+1) u (widen_ord (leqnSn n.+1) j) *
              v ord_max )))%Re).
    { nra. } rewrite H2. clear H2.
    apply Rplus_le_compat.
    * nra.
    * apply Rplus_le_le_0_compat.
      ++ apply Rmult_le_compat_0.
         - by apply /RleP.
         - apply /RleP. apply sum_n_ge_0. intros. by apply H0.
      ++ apply Rmult_le_compat_0.
         - apply /RleP. apply sum_n_ge_0. intros. by apply H.
         - by apply /RleP.
Qed.


Lemma big_sum_add: forall (n:nat) (u v: 'I_n.+1 ->R),
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
  rewrite -IHn. rewrite -!RplusE.
  assert ((\big[+%R/0]_(i < n.+1) u (widen_ord (leqnSn n.+1) i) +
             u ord_max +
             (\big[+%R/0]_(i < n.+1) v (widen_ord (leqnSn n.+1) i) +
              v ord_max))%Re =
           (\big[+%R/0]_(i < n.+1) u (widen_ord (leqnSn n.+1) i) +
            \big[+%R/0]_(i < n.+1) v (widen_ord (leqnSn n.+1) i) +
            (u ord_max + v ord_max))%Re).
  { nra. } rewrite H. by [].
Qed.


Lemma big_sqr_le: forall (n:nat) (u v : 'I_n.+1 -> R),
  (forall j:'I_n.+1, 0 <= u j) ->
  (forall j: 'I_n.+1, 0 <= v j) ->
  Rsqr (\big[+%R/0]_j ((u j * v j))) <=
  \big[+%R/0]_j (Rsqr (u j)) *
  \big[+%R/0]_j (Rsqr (v j)).
Proof.
intros. apply /RleP. induction n.
+ simpl. rewrite !big_ord_recr //= !big_ord0. rewrite !add0r.
  rewrite Rsqr_mult. apply /RleP. rewrite -RmultE. apply /RleP. nra.
+ simpl. rewrite big_ord_recr //=.
  assert (\big[+%R/0]_(j < n.+2) (u j)² =
            \big[+%R/0]_(j < n.+1) (u (widen_ord (leqnSn n.+1) j))² +
              Rsqr (u ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H1.
  assert (\big[+%R/0]_(j < n.+2) (v j)² =
            \big[+%R/0]_(j < n.+1) (v (widen_ord (leqnSn n.+1) j))² +
              Rsqr (v ord_max)).
  { by rewrite big_ord_recr //=. } rewrite H2.
  clear H1 H2. rewrite !mulrDr !mulrDl. apply /RleP.
  rewrite -!RplusE -!RmultE. rewrite Rsqr_plus.
  rewrite Rplus_assoc.
  assert ((\big[+%R/0]_(j < n.+1) (u (widen_ord (leqnSn n.+1) j))² *
             \big[+%R/0]_(j < n.+1) (v (widen_ord (leqnSn n.+1) j))² +
             (u ord_max)² *
             \big[+%R/0]_(j < n.+1) (v (widen_ord (leqnSn n.+1) j))² +
             (\big[+%R/0]_(j < n.+1) (u (widen_ord (leqnSn n.+1) j))² *
              (v ord_max)² + (u ord_max)² * (v ord_max)²))%Re =
           (\big[+%R/0]_(j < n.+1) (u (widen_ord (leqnSn n.+1) j))² *
             \big[+%R/0]_(j < n.+1) (v (widen_ord (leqnSn n.+1) j))² +
            (((u ord_max)² * (v ord_max)²) +
               ((u ord_max)² *
                  \big[+%R/0]_(j < n.+1) (v (widen_ord (leqnSn n.+1) j))² +
                (\big[+%R/0]_(j < n.+1) (u (widen_ord (leqnSn n.+1) j))² *
                  (v ord_max)²))))%Re).
  { nra. } rewrite H1. clear H1.
  apply /RleP. apply Rplus_le_compat.
  - by apply IHn.
  - rewrite Rsqr_mult.
    apply Rplus_le_compat_l.
    rewrite !big_distrr //= !big_distrl //=.
    apply /RleP. rewrite !RplusE. rewrite big_sum_add.
    apply big_sum_ge_ex_abstract. intros.
    rewrite -!RmultE. rewrite -!RplusE.
    assert ((2 *
               (u (widen_ord (leqnSn n.+1) i) *
                v (widen_ord (leqnSn n.+1) i)) *
               (u ord_max * v ord_max))%Re =
              (2 * (u ord_max *  v (widen_ord (leqnSn n.+1) i)) *
                   (u (widen_ord (leqnSn n.+1) i) * v ord_max))%Re).
    { nra. } rewrite H2.
    apply Rge_le. apply Rminus_ge. apply Rle_ge.
    rewrite -!Rsqr_mult. rewrite -Rsqr_minus.
    apply Rle_0_sqr.
Qed.



Lemma is_finite_bound (x:Rbar):
  (exists k l:R, Rbar_le x k /\ Rbar_le l x) ->
  is_finite x.
Proof.
intros. destruct H as [k H]. destruct H as [l H].
destruct H. unfold Rbar_le in H, H0.
destruct x.
+ by unfold is_finite.
+ by [].
+ by [].
Qed.


Lemma matrix_norm_is_finite: forall (n:nat) (A: 'M[complex R]_n.+1),
  is_finite (matrix_norm A).
Proof.
intros.
apply is_finite_bound.
exists (mat_norm A),0.
split.
+ rewrite /matrix_norm. unfold Lub_Rbar.
  destruct ex_lub_Rbar. simpl.
  unfold is_lub_Rbar in i. destruct i.
  unfold is_ub_Rbar in H. specialize (H0 (mat_norm A)).
  apply H0. unfold is_ub_Rbar. intros. destruct H1 as [v H1].
  destruct H1. rewrite H2.
  unfold Rbar_le. rewrite -RdivE.
  - assert (mat_norm A = ((mat_norm A * vec_norm_C v) * (/ vec_norm_C v))%Re).
    { assert (((mat_norm A * vec_norm_C v) * (/ vec_norm_C v))%Re =
                (mat_norm A * (vec_norm_C v * /vec_norm_C v))%Re).
      { nra. } rewrite H3.
      assert ((vec_norm_C v * /vec_norm_C v)%Re = 1%Re).
      { apply Rinv_r. apply non_zero_vec_norm.
        assert (exists i, v i 0 != 0).
        { by apply /cV0Pn. } unfold vec_not_zero. destruct H4 as [i H4].
        exists i. by apply /eqP.
      } rewrite H4. nra.
    } rewrite H3.
    apply Rmult_le_compat.
    + apply vec_norm_C_ge_0.
    + apply Rlt_le. apply Rinv_0_lt_compat. apply vec_norm_gt_0.
      assert (exists i, v i 0 != 0).
      { by apply /cV0Pn. } unfold vec_not_zero. destruct H4 as [i H4].
      exists i. by apply /eqP.
    + rewrite /vec_norm_C /mat_norm. rewrite Rmult_comm.
      rewrite -sqrt_mult_alt.
      - apply sqrt_le_1.
        * apply /RleP. apply big_ge_0_ex_abstract. intros.
          apply /RleP. apply Rsqr_ge_0. apply C_mod_ge_0.
        * rewrite big_distrl //=. apply /RleP. apply sum_n_ge_0.
          intros. apply /RleP. apply Rmult_le_pos.
          ++ apply Rsqr_ge_0. apply C_mod_ge_0.
          ++ apply /RleP. apply sum_n_ge_0. intros.
             apply sum_n_ge_0. intros. apply /RleP. apply Rsqr_ge_0.
             apply C_mod_ge_0.
        * rewrite big_distrr //=. apply /RleP.
          apply big_sum_ge_ex_abstract. intros. rewrite mxE.
          apply Rle_trans with
            (Rsqr (\big[+%R/0]_j ((C_mod ((A i j * v j 0)%Ri))))).
          ++ apply Rsqr_incr_1.
             - apply /RleP. apply C_mod_sum_rel.
             - apply C_mod_ge_0.
             - apply /RleP. apply big_ge_0_ex_abstract. intros.
               apply /RleP. apply C_mod_ge_0.
             - assert (\big[+%R/0]_j C_mod (A i j * v j 0)%Ri =
                        \big[+%R/0]_j ((C_mod (A i j)) * (C_mod (v j 0)))).
               { apply eq_big. by []. intros. by rewrite C_mod_prod. }
               rewrite H5. apply /RleP. rewrite RmultE.  rewrite mulrC.
               rewrite -!RmultE.
               apply (@big_sqr_le _ (fun j => C_mod (A i j)) (fun j => C_mod (v j 0))).
               * intros. apply /RleP. apply C_mod_ge_0.
               * intros. apply /RleP. apply C_mod_ge_0.
       - apply /RleP. apply big_ge_0_ex_abstract. intros.
         apply /RleP. apply Rsqr_ge_0. apply C_mod_ge_0.
     + nra.
  - apply /eqP. apply non_zero_vec_norm.
    unfold vec_not_zero.
    assert (exists i, v i 0 != 0). { by apply /cV0Pn. }
    destruct H3 as [i H3]. exists i. by apply /eqP.
+ apply matrix_norm_ge_0_aux .
Qed.


Lemma matrix_norm_ge_0:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  (0 <= matrix_norm A)%Re.
Proof.
intros.
assert (is_finite (matrix_norm A)). { apply matrix_norm_is_finite. }
assert (Rbar_le 0%Re (matrix_norm A)).
{ apply matrix_norm_ge_0_aux . }
unfold Rbar_le in H0. apply is_finite_correct in H.
destruct H. rewrite H in H0. by rewrite H.
Qed.


(** ||Ax|| <= ||A|| ||x|| **)
Lemma matrix_norm_compat_aux:
  forall (n:nat) (x: 'cV[complex R]_n.+1) (A: 'M[complex R]_n.+1),
    x != 0 ->
    Rbar_le (vec_norm_C (A *m x) / vec_norm_C x)%Re (matrix_norm A).
Proof.
intros. rewrite /matrix_norm.
rewrite /Lub_Rbar. destruct ex_lub_Rbar.
simpl. rewrite /is_lub_Rbar in i.
destruct i. unfold is_ub_Rbar in H0.
unfold Rbar_le in H0. apply H0. intros.
exists x. split.
+ by [].
+ rewrite -RdivE.
  - by [].
  - apply /eqP.
    apply non_zero_vec_norm.
    unfold vec_not_zero.
    assert (exists i : 'I_n.+1, x i 0 != 0).
    { by apply /cV0Pn. } destruct H2 as [i H2].
    exists i. by apply /eqP.
Qed.


Lemma matrix_norm_compat:
  forall (n:nat) (x: 'cV[complex R]_n.+1) (A: 'M[complex R]_n.+1),
    x != 0 ->
    vec_norm_C (mulmx A x) <= ((matrix_norm A) * vec_norm_C x)%Re.
Proof.
intros.
assert (is_finite (matrix_norm A)). { apply matrix_norm_is_finite. }
assert (Rbar_le (vec_norm_C (A *m x) / vec_norm_C x)%Re (matrix_norm A)).
{ by apply matrix_norm_compat_aux. }
unfold Rbar_le in H1. apply is_finite_correct in H0.
destruct H0. rewrite H0 in H1. rewrite H0. apply /RleP.
assert (vec_norm_C (A *m x) = (vec_norm_C (A *m x) * (/vec_norm_C x * vec_norm_C x))%Re).
{ assert ((/ vec_norm_C x * vec_norm_C x)%Re = 1%Re).
  { apply Rinv_l.
    apply non_zero_vec_norm.
    unfold vec_not_zero.
    assert (exists i : 'I_n.+1, x i 0 != 0).
    { by apply /cV0Pn. } destruct H2 as [i H2].
    exists i. by apply /eqP.
  } rewrite H2. nra.
} rewrite H2.
assert ((vec_norm_C (A *m x) * (/ vec_norm_C x * vec_norm_C x))%Re =
        ((vec_norm_C (A *m x) * / vec_norm_C x) * (vec_norm_C x))%Re).
{ nra. } rewrite H3.
apply Rmult_le_compat_r.
+ apply vec_norm_C_ge_0.
+ apply H1.
Qed.


Lemma vec_norm_col_row_compat: forall (n:nat) (x: 'rV[complex R]_n.+1),
  vec_norm_rowv x = vec_norm_C x^T.
Proof.
intros.
rewrite /vec_norm_rowv /vec_norm_C.
assert (\big[+%R/0]_l (C_mod (x 0 l))² = \big[+%R/0]_l (C_mod (x^T l 0))²).
{ apply eq_big. by []. intros. by rewrite mxE. }
by rewrite H.
Qed.


Lemma vec_norm_C_conv:
  forall (n:nat) (x: 'rV[complex R]_n.+1) (A: 'M[complex R]_n.+1),
  vec_norm_C (x *m A)^T  = vec_norm_C (A^T *m x^T).
Proof.
intros. rewrite /vec_norm_C.
assert (\big[+%R/0]_l (C_mod ((x *m A)^T l 0))² =
        \big[+%R/0]_l (C_mod ((A^T *m x^T) l 0))²).
{ apply eq_big. by []. intros. rewrite !mxE.
  assert ( (\big[+%R/0]_j (x 0 j * A j i)) = (\big[+%R/0]_j (A^T i j * x^T j 0))).
  { apply eq_big. by []. intros. by rewrite !mxE mulrC. }
  by rewrite H0.
} by rewrite H.
Qed.

Lemma Rbar_le_mult_compat: forall (x y:R) (z r: Rbar),
  (0 <= x)%Re -> (0 <= y)%Re ->
  Rbar_le x z -> Rbar_le y r ->
  Rbar_le (x * y)%Re (Rbar_mult z r).
Proof.
intros. destruct z.
+ destruct r.
  - rewrite /Rbar_mult /Rbar_le. simpl.
    by apply Rmult_le_compat.
  - unfold Rbar_le in H1.
    assert ((0<=r0)%Re).
    { by apply Rle_trans with x. }
    assert (r0 = 0%Re \/ (0<r0)%Re). { nra. } destruct H4.
    * rewrite H4. rewrite Rbar_mult_0_l.
      assert (x = 0%Re \/ (0<x)%Re).
      { nra. } destruct H5.
      ++ rewrite H5. unfold Rbar_le. nra.
      ++ rewrite H4 in H1. contradict H1. nra.
    * assert (Rbar_mult r0 p_infty = p_infty).
      { rewrite Rbar_mult_comm. apply is_Rbar_mult_unique.
        apply is_Rbar_mult_p_infty_pos. by unfold Rbar_lt.
      } rewrite H5. by unfold Rbar_le.
  - by unfold Rbar_le in H2.
+ destruct r.
  - unfold Rbar_le in H2.
    assert ((0<=r)%Re).
    { by apply Rle_trans with y. }
    assert (r = 0%Re \/ (0<r)%Re). { nra. } destruct H4.
    * rewrite H4.  rewrite Rbar_mult_0_r.
      assert (y = 0%Re \/ (0<y)%Re).
      { nra. } destruct H5.
      ++ rewrite H5. unfold Rbar_le. nra.
      ++ rewrite H4 in H2. contradict H2. nra.
    * assert (Rbar_mult p_infty r = p_infty).
      { apply is_Rbar_mult_unique.
        apply is_Rbar_mult_p_infty_pos. by unfold Rbar_lt.
      } rewrite H5. by unfold Rbar_le.
    * assert ( Rbar_mult p_infty p_infty = p_infty).
      { apply is_Rbar_mult_unique.
        apply is_Rbar_mult_p_infty_pos. by unfold Rbar_lt.
      } rewrite H3. by unfold Rbar_le.
  - by unfold Rbar_le in H2.
  - by unfold Rbar_le in H1.
Qed.

Lemma big_0_implies_all_0: forall (n:nat) (x : 'I_n.+1 -> complex R),
  \big[+%R/0]_l (C_mod (x l))² = 0%Re ->
  (forall l: 'I_n.+1, x l = 0).
Proof.
intros.
induction n.
+ simpl in H. rewrite big_ord_recl //= big_ord0 addr0 in H.
  apply Rsqr_eq_0 in H. apply C_mod_eq_0 in H.
  assert (l = ord0). { by apply ord1. } by rewrite H0.
+ rewrite big_ord_recr //= in H. rewrite -RplusE in H.
  apply Rplus_eq_R0 in H. destruct H.
  - specialize (IHn _ H).
    apply Rsqr_eq_0 in H0. apply C_mod_eq_0 in H0.
    assert ((l < n.+2)%N). { by []. }
    assert ((l < n.+1)%N \/ l = ord_max).
    { rewrite leq_eqVlt in H1.
      assert ((l.+1 == n.+2) \/ (l.+1 < n.+2)%N).
      { by apply /orP. } destruct H2.
      + right. by apply /eqP.
      + by left.
    } destruct H2.
    * specialize (IHn (@inord n l)). simpl in IHn.
      assert (l = (widen_ord (leqnSn n.+1) (inord l)) :> nat).
      { rewrite /widen_ord //=. by rewrite inordK. }
      assert (inord l = l). { by rewrite inord_val. }
      rewrite -H4. rewrite H3. by rewrite inord_val.
    * by rewrite H2.
  - apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
  - apply Rle_0_sqr.
Qed.

Lemma sqrt_not_0: forall (x:R), sqrt x <> 0 -> x <> 0.
Proof.
intros.
assert (x = 0 \/ x <> 0).
{ nra. } destruct H0.
+ rewrite H0 in H. rewrite sqrt_0 in H. by contradict H.
+ apply H0.
Qed.

Lemma Rsqr_not_0: forall (x:R), Rsqr x <> 0 -> x <> 0.
Proof.
intros.
assert (x = 0 \/ x <> 0).
{ nra. } destruct H0.
+ rewrite H0 in H. rewrite Rsqr_0 in H. by contradict H.
+ apply H0.
Qed.

Lemma sum_not_zero:
  forall (x y:R), (x + y)%Re <> 0 -> x <> 0%Re \/ y <> 0%Re.
Proof.
intros.
assert (x = 0%Re \/ x <> 0%Re).
{ nra. } destruct H0.
+ rewrite H0 in H. right.
  assert ((0 + y)%Re = y). { nra. } by rewrite H1 in H.
+ by left.
Qed.

Lemma big_0_implies_not_0: forall (n:nat) (x : 'I_n.+1 -> complex R),
  \big[+%R/0]_l (C_mod (x l))² <> 0%Re ->
  (exists l: 'I_n.+1, x l <> 0).
Proof.
intros. induction n.
+ simpl in H. rewrite big_ord_recl //= big_ord0 addr0 in H.
  exists (ord0). rewrite C_mod_gt_0. apply C_mod_gt_not_zero.
  by apply Rsqr_not_0.
+ rewrite big_ord_recr //= in H. rewrite -RplusE in H.
  apply sum_not_zero in H.
  destruct H.
  - specialize (IHn _ H). destruct IHn as [i IHn].
    exists (widen_ord (leqnSn n.+1) i). by apply IHn.
  - exists ord_max. apply Rsqr_not_0 in H. apply C_mod_gt_not_zero in H.
    by apply C_mod_gt_0.
Qed.


Lemma vec_is_zero_or_not:
  forall (n:nat) (x : 'cV[complex R]_n.+1), x = 0 \/ x != 0.
Proof.
intros.
assert (vec_norm_C x = 0%Re \/ vec_norm_C x <> 0%Re).
{ nra. } destruct H.
+ left. apply matrixP. unfold eqrel. intros.
  rewrite /vec_norm_C in H. apply sqrt_eq_0 in H.
  - rewrite [RHS]mxE. move: x0. apply big_0_implies_all_0.
    assert (y = 0). { by apply ord1. } by rewrite H0.
  - apply /RleP. apply sum_n_ge_0. intros. apply /RleP. apply Rle_0_sqr.
+ right. rewrite /vec_norm_C in H. apply /cV0Pn.
  apply sqrt_not_0 in H. apply big_0_implies_not_0 in H.
  destruct H as [l H]. exists l. by apply /eqP.
Qed.


Lemma matrix_norm_prod_aux:
  forall (n:nat) (A B: 'M[complex R]_n.+1),
  Rbar_le (matrix_norm (A *m B)) (Rbar_mult (matrix_norm A) (matrix_norm B)).
Proof.
intros. rewrite /matrix_norm.
rewrite /Lub_Rbar. destruct ex_lub_Rbar.
simpl. rewrite /is_lub_Rbar in i.
destruct i.  unfold is_ub_Rbar in H.
destruct ex_lub_Rbar. simpl. rewrite /is_lub_Rbar in i.
destruct i. unfold is_ub_Rbar in H1.
destruct ex_lub_Rbar. simpl. rewrite /is_lub_Rbar in i.
destruct i. unfold is_ub_Rbar in H3.
specialize (H0 (Rbar_mult x0 x1)).
apply H0.
unfold is_ub_Rbar.
intros.
destruct H5 as [v H5]. destruct H5.
assert (B *m v = 0 \/ B *m v != 0).
{ by apply vec_is_zero_or_not. } destruct H7.
- rewrite -mulmxA in H6. rewrite H7 in H6.
  assert (vec_norm_C (A *m 0) = 0).
  { rewrite /vec_norm_C.
    assert (\big[+%R/0]_l (C_mod ((@mulmx _ n.+1 n.+1 1 A 0) l 0))² = 0%Re).
    { rewrite -(big_0_sum n). apply eq_big. by []. intros.
      rewrite !mxE.
      assert (\big[+%R/0]_j (A i j * (0 : 'M[complex R]_(n.+1,1)) j 0) = 0).
      { rewrite -[RHS](big_0_sum_0 n.+1). apply eq_big. by [].
        intros. by rewrite mxE mulr0.
      } rewrite H9.
      by rewrite C_mod_0 Rsqr_0.
    } rewrite H8. by rewrite sqrt_0.
  } rewrite H8 in H6. rewrite -RdivE in H6.
  * assert ((0 / vec_norm_C v)%Re = 0%Re).
    { nra. } rewrite H9 in H6. rewrite H6.
    clear H6 H9.
    assert (0%Re = (0 * 0)%Re). { nra. } rewrite H6.
    apply Rbar_le_mult_compat.
    ++ nra.
    ++ nra.
    ++ specialize (H1 ((vec_norm_C (A *m ((one_vec n)))) / (vec_norm_C (one_vec n)))%Re).
       apply Rbar_le_trans with
        ((vec_norm_C (A *m ((one_vec n)))) / (vec_norm_C (one_vec n)))%Re.
       - unfold Rbar_le.
         rewrite one_vec_norm_1.
         assert ((vec_norm_C (A *m one_vec n) / 1)%Re = vec_norm_C (A *m one_vec n)).
         { nra. } rewrite H9. apply vec_norm_C_ge_0.
       - apply H1. exists (one_vec n). split.
         * apply /cV0Pn. exists 0. rewrite mxE //=. by rewrite oner_neq0.
         * rewrite -RdivE.
           -- by [].
           -- rewrite one_vec_norm_1. apply oner_neq0.
    ++ specialize (H3 ((vec_norm_C (B *m ((one_vec n)))) / (vec_norm_C (one_vec n)))%Re).
       apply Rbar_le_trans with
        ((vec_norm_C (B *m ((one_vec n)))) / (vec_norm_C (one_vec n)))%Re.
       - unfold Rbar_le.
         rewrite one_vec_norm_1.
         assert ((vec_norm_C (B *m one_vec n) / 1)%Re = vec_norm_C (B *m one_vec n)).
         { nra. } rewrite H9. apply vec_norm_C_ge_0.
       - apply H3. exists (one_vec n). split.
         * apply /cV0Pn. exists 0. rewrite mxE //=. by rewrite oner_neq0.
         * rewrite -RdivE.
           -- by [].
           -- rewrite one_vec_norm_1. apply oner_neq0.
  * apply /eqP. apply non_zero_vec_norm.
    assert (exists i, v i 0 != 0).
    { by apply /cV0Pn. } unfold vec_not_zero. destruct H6 as [i H6].
    exists i. by apply /eqP.
- specialize (H3 (vec_norm_C (B *m v) / (vec_norm_C v))%Re).
  specialize (H1 (vec_norm_C (A *m (B *m v)) / (vec_norm_C (B *m v)))%Re).
  apply Rbar_le_trans with
    ((vec_norm_C (A *m (B *m v)) / (vec_norm_C (B *m v)))%Re *
      (vec_norm_C (B *m v) / (vec_norm_C v))%Re)%Re.
  + rewrite H6.
    assert ( (vec_norm_C (A *m (B *m v)) / vec_norm_C (B *m v) *
                (vec_norm_C (B *m v) / vec_norm_C v))%Re =
            (vec_norm_C (A *m B *m v) / vec_norm_C v)).
    { assert ((vec_norm_C (A *m (B *m v)) / vec_norm_C (B *m v) *
                (vec_norm_C (B *m v) / vec_norm_C v))%Re =
               ((vec_norm_C (A *m B *m v) / vec_norm_C v) *
               (vec_norm_C (B *m v) * / vec_norm_C (B *m v)))%Re).
      { rewrite mulmxA. nra. } rewrite H8.
      assert ((vec_norm_C (B *m v) * / vec_norm_C (B *m v))%Re = 1%Re).
      { apply Rinv_r. apply non_zero_vec_norm.
        unfold vec_not_zero.
        assert (exists i, (B *m v) i 0 != 0).
        { by apply /cV0Pn. } destruct H9 as [i H9]. exists i.
        by apply /eqP.
        } rewrite H9. rewrite -RdivE.
      nra. apply /eqP. apply non_zero_vec_norm.
      assert (exists i, v i 0 != 0).
      { by apply /cV0Pn. } unfold vec_not_zero. destruct H10 as [i H10].
      exists i. by apply /eqP.
    } rewrite H8. apply Rbar_le_refl.
  + apply Rbar_le_mult_compat.
    - assert ( 0%Re = (0 * 0)%Re). { nra. } rewrite H8.
      apply Rmult_le_compat.
      * nra.
      * nra.
      * apply vec_norm_C_ge_0.
      * apply Rlt_le. apply Rinv_0_lt_compat.
        apply vec_norm_gt_0.
        unfold vec_not_zero.
        assert (exists i, (B *m v) i 0 != 0).
        { by apply /cV0Pn. } destruct H9 as [i H9]. exists i.
        by apply /eqP.
    - assert ( 0%Re = (0 * 0)%Re). { nra. } rewrite H8.
      apply Rmult_le_compat.
      * nra.
      * nra.
      * apply vec_norm_C_ge_0.
      * apply Rlt_le. apply Rinv_0_lt_compat.
        apply vec_norm_gt_0. unfold vec_not_zero.
        assert (exists i, v i 0 != 0).
        { by apply /cV0Pn. } destruct H9 as [i H9].
        exists i. by apply /eqP.
    - apply H1.
      exists (B *m v). split.
      * by [].
      * rewrite -RdivE.
        ++ by [].
        ++ apply /eqP. apply non_zero_vec_norm.
            unfold vec_not_zero.
            assert (exists i, (B *m v) i 0 != 0).
            { by apply /cV0Pn. } destruct H8 as [i H8]. exists i.
            by apply /eqP.
    - apply H3. exists v. split.
      * apply H5.
      * rewrite -RdivE.
        ++ by [].
        ++ apply /eqP. apply non_zero_vec_norm.
           unfold vec_not_zero.
           assert (exists i, v i 0 != 0).
           { by apply /cV0Pn. } destruct H8 as [i H8].
           exists i. by apply /eqP.
Qed.


Lemma matrix_norm_prod:
  forall (n:nat) (A B: 'M[complex R]_n.+1),
  (matrix_norm (A *m B) <= (matrix_norm A) * (matrix_norm B))%Re.
Proof.
intros.
assert (is_finite (matrix_norm A)). { apply matrix_norm_is_finite. }
assert (is_finite (matrix_norm B)). { apply matrix_norm_is_finite. }
assert (is_finite (matrix_norm (A *m B))). { apply matrix_norm_is_finite. }
assert (Rbar_le (matrix_norm (A *m B)) (Rbar_mult (matrix_norm A) (matrix_norm B))).
{ by apply matrix_norm_prod_aux. }
unfold Rbar_le in H2.
apply is_finite_correct in H.
apply is_finite_correct in H0.
apply is_finite_correct in H1.
destruct H,H0,H1. rewrite H H0 H1 in H2. unfold Rbar_mult in H2. simpl in H2.
by rewrite H H0 H1.
Qed.





(** 2 norm of a matrix <= Frobenius norm of the matrix **)
Lemma mat_2_norm_F_norm_compat:
  forall (n:nat) (A: 'M[complex R]_n.+1),
  (0 <= matrix_norm A <= mat_norm A)%Re.
Proof.
intros.
assert (is_finite (matrix_norm A)). { apply matrix_norm_is_finite. }
split.
+ by apply matrix_norm_ge_0.
+ assert (Rbar_le (matrix_norm A) (mat_norm A) ->
          (matrix_norm A <= mat_norm A)%Re).
  { unfold Rbar_le. apply is_finite_correct in H.
    destruct H. by rewrite H.
  } apply H0.
  unfold matrix_norm. rewrite /Lub_Rbar. destruct ex_lub_Rbar.
  simpl. unfold is_lub_Rbar in i. destruct i.
  unfold is_ub_Rbar in H1. specialize (H2 (mat_norm A)).
  apply H2. unfold is_ub_Rbar. intros.
  destruct H3 as [v H3]. destruct H3. rewrite H4.
  unfold Rbar_le. rewrite -RdivE.
  - assert (mat_norm A = ((mat_norm A * vec_norm_C v) * (/ vec_norm_C v))%Re).
    { assert (((mat_norm A * vec_norm_C v) * (/ vec_norm_C v))%Re =
                (mat_norm A * (vec_norm_C v * /vec_norm_C v))%Re).
      { nra. } rewrite H5.
      assert ((vec_norm_C v * /vec_norm_C v)%Re = 1%Re).
      { apply Rinv_r. apply non_zero_vec_norm.
        assert (exists i, v i 0 != 0).
        { by apply /cV0Pn. } unfold vec_not_zero. destruct H6 as [i H6].
        exists i. by apply /eqP.
      } rewrite H6. nra.
    } rewrite H5.
    apply Rmult_le_compat.
    + apply vec_norm_C_ge_0.
    + apply Rlt_le. apply Rinv_0_lt_compat. apply vec_norm_gt_0.
      assert (exists i, v i 0 != 0).
      { by apply /cV0Pn. } unfold vec_not_zero. destruct H6 as [i H6].
      exists i. by apply /eqP.
    + rewrite /vec_norm_C /mat_norm. rewrite Rmult_comm.
      rewrite -sqrt_mult_alt.
      - apply sqrt_le_1.
        * apply /RleP. apply big_ge_0_ex_abstract. intros.
          apply /RleP. apply Rsqr_ge_0. apply C_mod_ge_0.
        * rewrite big_distrl //=. apply /RleP. apply sum_n_ge_0.
          intros. apply /RleP. apply Rmult_le_pos.
          ++ apply Rsqr_ge_0. apply C_mod_ge_0.
          ++ apply /RleP. apply sum_n_ge_0. intros.
             apply sum_n_ge_0. intros. apply /RleP. apply Rsqr_ge_0.
             apply C_mod_ge_0.
        * rewrite big_distrr //=. apply /RleP.
          apply big_sum_ge_ex_abstract. intros. rewrite mxE.
          apply Rle_trans with
            (Rsqr (\big[+%R/0]_j ((C_mod ((A i j * v j 0)%Ri))))).
          ++ apply Rsqr_incr_1.
             - apply /RleP. apply C_mod_sum_rel.
             - apply C_mod_ge_0.
             - apply /RleP. apply big_ge_0_ex_abstract. intros.
               apply /RleP. apply C_mod_ge_0.
             - assert (\big[+%R/0]_j C_mod (A i j * v j 0)%Ri =
                        \big[+%R/0]_j ((C_mod (A i j)) * (C_mod (v j 0)))).
               { apply eq_big. by []. intros. by rewrite C_mod_prod. }
               rewrite H7. apply /RleP. rewrite RmultE.  rewrite mulrC.
               rewrite -!RmultE.
               apply (@big_sqr_le _ (fun j => C_mod (A i j)) (fun j => C_mod (v j 0))).
               * intros. apply /RleP. apply C_mod_ge_0.
               * intros. apply /RleP. apply C_mod_ge_0.
       - apply /RleP. apply big_ge_0_ex_abstract. intros.
         apply /RleP. apply Rsqr_ge_0. apply C_mod_ge_0.
     + nra.
  - apply /eqP. apply non_zero_vec_norm.
    unfold vec_not_zero.
    assert (exists i, v i 0 != 0). { by apply /cV0Pn. }
    destruct H5 as [i H5]. exists i. by apply /eqP.
Qed.


