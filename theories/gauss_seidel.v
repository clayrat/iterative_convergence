(** Proof the Reich theorem for the Gauss-Seidel iteration **)

Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop ssrnat.
From mathcomp Require Import mxalgebra matrix all_field vector.
From mathcomp.analysis Require Import boolp Rstruct classical_sets signed.
From Coquelicot Require Import Lim_seq Rbar Hierarchy Lub.
Require Import complex_mat_vec_prop.
Require Import iter_necessity iter_convergence.

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

(** Definition of a symmetric matrix **)
Definition symmetric (n:nat) (A: 'M[complex R]_n.+1):=
  forall i j:'I_n.+1, A i j = A j i.

(** Definition of a positive definite matrix **)
Definition is_positive_definite (n:nat) (A: 'M[R]_n.+1):=
  forall (x: 'cV[complex R]_n.+1),  x != 0 ->
    Re (mulmx (conjugate_transpose x) (mulmx (RtoC_mat A) x) 0 0) >0.


(* Lower triangular matrix *)
Definition A1 (n:nat) (A: 'M[R]_n):= \matrix_(i<n, j<n)
  if (leb j i) then A i j else 0.

(* Upper triangular matrix *)
Definition A2 (n:nat) (A: 'M[R]_n):= \matrix_(i<n, j<n)
  if (i<j)%nat then A i j else 0.


Definition d (n:nat) (A: 'M[R]_n):= \row_(i<n) A i i.

(** Diagonal matrix from A**)
Definition diag_A (n:nat) (A: 'M[R]_n):=diag_mx (d A).


Lemma diag_prod: forall (n:nat) (d:'rV[R]_n) (x: 'cV[R]_n),
  mulmx (diag_mx d) x = \col_i (d 0 i * x i 0).
Proof.
intros. apply matrixP. unfold eqrel. intros.
rewrite !mxE. rewrite (bigD1 x0) //=. unfold diag_mx. rewrite !mxE.
rewrite eqxx //=. rewrite big1. rewrite addr0 //.
assert (y= 0). { apply ord1. }
rewrite H. by [].
intros. rewrite mxE. rewrite eq_sym. rewrite mulrnAl.
assert (i==x0  = false). { by apply negbTE. }
by rewrite H0.
Qed.


Lemma diag_prod_C: forall (n:nat) (d:'rV[R]_n) (x: 'cV[complex R]_n),
  mulmx (RtoC_mat (diag_mx d)) x = \col_i (RtoC (d 0 i) * x i 0).
Proof.
intros.
unfold RtoC_mat. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite (bigD1 x0) //=. unfold diag_mx. rewrite !mxE.
rewrite eqxx //=. rewrite big1. rewrite addr0 //.
assert (y= 0). { apply ord1. }
rewrite H. by [].
intros. rewrite !mxE. rewrite eq_sym.
assert (x i y = (Re (x i y) +i* Im (x i y))%C).
{ apply C_destruct. } rewrite H0 //=. apply /eqP.
rewrite eq_complex //=. apply /andP.
assert (i==x0  = false). { by apply negbTE. }
rewrite H1 //= !mulr0n !mul0r sub0r add0r.
split.
+ apply /eqP. assert ( (-0)%Re = 0%Re). { nra. } by apply H2.
+ by [].
Qed.


(** Proof that if the diagonal entries of A are positive then
  the diagonal matrix from A is positive definite **)
Lemma is_positive_definite_diag:
  forall (n:nat) (A: 'M[R]_n.+1),
   (forall i:'I_n.+1,  A i i > 0) ->
   is_positive_definite (diag_A A).
Proof.
intros. rewrite /is_positive_definite /diag_A. intros. rewrite diag_prod_C.
intros. rewrite /conjugate_transpose /transpose_C.
rewrite /conjugate /RtoC_mat !mxE /RtoC.
have diag_simpl: (\big[+%R/0]_j
      ((\matrix_(i, j0) (\matrix_(i0, j1) ((x i0 j1)^*)%C)
                          j0 i) 0 j *
       (\col_i ((d A 0 i +i* 0)%C * x i 0)) j 0))
        =
      \big[+%R/0]_j ((conjc (x j 0))*(RtoC (A j j) * (x j 0))).
{ apply eq_big. by []. intros. by rewrite !mxE /RtoC. }
rewrite diag_simpl -eq_big_Re_C.
assert (\big[+%R/0]_(j < succn n) Re
                            (((x j 0)^*)%C *
                             (RtoC (A j j) * x j 0)) =
        \big[+%R/0]_(j < succn n) Re
                            ((((x j 0)^*) * (x j 0))%C *
                             (RtoC (A j j)))).
{ apply eq_big. by []. intros. rewrite mulrC.
  assert ((RtoC (A i i) * x i 0 * ((x i 0)^*)%C) =
            (RtoC (A i i) * (x i 0 * ((x i 0)^*)%C))).
  { by rewrite mulrA. } rewrite H2. rewrite mulrC.
  assert ((((x i 0)^*) * (x i 0))%C = ((x i 0) * ((x i 0)^*))%C).
  { by rewrite mulrC. } by rewrite H3.
} rewrite H1.
assert ( \big[+%R/0]_(j < succn n) Re
                            ((((x j 0)^*) * (x j 0))%C *
                             (RtoC (A j j))) =
        \big[+%R/0]_(j < succn n)
                            (Re(((x j 0)^*) * (x j 0))%C *
                              Re (RtoC (A j j)))).
{ apply eq_big. by []. intros. rewrite Re_complex_prod //=.
  by rewrite mulr0 subr0.
} rewrite H2.
assert (exists i, x i 0 != 0).
{ by apply /cV0Pn. }
destruct H3 as [i H3].
rewrite (bigD1 i) //=. apply /RltP.
rewrite -RplusE.
apply Rplus_lt_le_0_compat.
+ rewrite -RmultE. apply Rmult_lt_0_compat.
  - rewrite mulrC conj_mag /=. apply Rsqr_pos_lt.
    apply C_mod_not_zero. by apply /eqP.
  - by apply /RltP.
+ apply /RleP. apply big_ge_0_ex_abstract.
  intros. apply /RleP. rewrite -RmultE.
  apply Rmult_le_compat_0.
  - rewrite mulrC conj_mag /=. apply Rle_0_sqr.
  - apply Rlt_le. by apply /RltP.
Qed.

(** If the diagonal entries are not zero, then the
  inverse of A1 exists **)
Definition A1_inverse_exists (n:nat) (A: 'M[complex R]_n.+1):=
  forall i:'I_n.+1, A i i <> 0.


(*** Matrix equality ***)
Lemma matrix_eq:
  forall (n m p:nat) (A: 'M[complex R]_(m,n))
    (B: 'M[complex R]_(m,n)) (C: 'M[complex R]_(p,m)),
   A = B -> mulmx C A = mulmx C B.
Proof.
intros. rewrite H. reflexivity.
Qed.

(** Define the conjugate transpose of A1 **)
Lemma conj_transpose_A1: forall (n:nat) (A: 'M[R]_n),
    conjugate_transpose (RtoC_mat (A1 A)) = transpose_C (RtoC_mat (A1 A)).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite /conjc. apply /eqP. rewrite eq_complex //=. apply /andP.
split.
+ by apply /eqP.
+ apply /eqP. by rewrite oppr0.
Qed.

(** Define the transpose of  a real matrix **)
Definition transpose_R (m n:nat) (A: 'M[R]_(m,n)):=
  \matrix_(i<n,j<m) A j i.

(** transpose of A1 = D + A2 **)
Lemma A1_split: forall (n:nat) (A :'M[R]_n.+1),
    (forall (i j:'I_n.+1), A i j = A j i)->
    transpose_R (A1 A) = addmx  (diag_A A) (A2 A).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
assert ((x<=y)%N \/ (x>=y)%N). { apply /orP. apply leq_total. } destruct H0.
+ assert (x <=? y = true).
  { apply leb_correct. apply /ssrnat.leP. apply H0. }
  rewrite H1.
  assert (x== y \/ (x<y)%N). { apply /orP. rewrite -leq_eqVlt. apply H0. }
  destruct H2.
  - rewrite H2 /=.
    assert ( x = y). { apply /eqP. apply H2. } rewrite H3.
    assert ((y < y)%N = false). { apply ltnn. }
    rewrite H4. rewrite addr0. by [].
  - assert (x==y = false). { by apply ltn_eqF. } rewrite H3. simpl.
    assert ((x < y)%N = true). { by []. } rewrite H4.
    specialize (H x y). rewrite H. rewrite mulr0n. by rewrite add0r.
+ assert ( y == x \/ (y<x)%N). { apply /orP. rewrite -leq_eqVlt. apply H0. }
  destruct H1.
  - assert (y= x). { by apply /eqP. } rewrite H2.
    assert ((x <=? x)%N = true). { apply leb_correct. lia. } rewrite H3.
    rewrite eqxx //=. assert ((x < x)%N = false).  { apply ltnn. } rewrite H4.
    by rewrite addr0.
  - assert ((x <=? y)%N = false). { apply leb_correct_conv. apply /ssrnat.ltP. apply H1. }
    rewrite H2.
    assert ((x == y) = false). { apply gtn_eqF. apply H1. } rewrite H3 //=.
    assert ((x < y)%N = false). { apply leq_gtF. apply H0. } rewrite H4.
    rewrite mulr0n. by rewrite add0r.
Qed.


Lemma RtoC_A1_prop : forall (n:nat) (A: 'M[R]_n.+1 ),
  transpose_C (RtoC_mat (A1 A)) = RtoC_mat (transpose_R (A1 A)).
Proof.
intros. apply matrixP. unfold eqrel. intros. by rewrite !mxE.
Qed.

(** A1 ^T = D + A2 **)
Lemma A1_tr_split_C: forall (n:nat) (A: 'M[R]_n.+1),
  (forall (i j:'I_n.+1), A i j =  A j i)->
  transpose_C (RtoC_mat (A1 A)) =
    addmx ( RtoC_mat (diag_A A)) (RtoC_mat (A2 A)).
Proof.
intros.
assert (transpose_C (RtoC_mat (A1 A)) = RtoC_mat (transpose_R (A1 A))).
{ apply RtoC_A1_prop. } rewrite H0.
assert ( RtoC_mat (addmx  (diag_A A) (A2 A)) =
          addmx (RtoC_mat (diag_A A)) (RtoC_mat (A2 A))).
{ by rewrite -RtoC_mat_add. } rewrite <-H1.
assert (transpose_R (A1 A) = addmx  (diag_A A) (A2 A)).
{ apply A1_split. apply H. }
by rewrite H2.
Qed.


Lemma Mplus_add_mat_eq:
  forall (m n:nat) (A B C: 'M[complex R]_(m,n)),
  A = B -> addmx A C = addmx B C.
Proof.
intros. rewrite H. reflexivity.
Qed.


Lemma Mplus_opp_r_C: forall (m n:nat) (A: 'M[complex R]_(m,n)),
  addmx A (oppmx A) = 0.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
by rewrite addrC addNr.
Qed.


Lemma Mplus_zero_r_C: forall (m n:nat) (A: 'M[complex R]_(m,n)),
  addmx A 0 =A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. by rewrite addr0.
Qed.



Lemma conjugate_transpose_const
  (n:nat) (l:complex R) (vi: 'cV[complex R]_n.+1) (A: 'M[R]_n.+1):
  Re ((conjugate_transpose (l *: vi) *m
      (RtoC_mat A *m (l *: vi))) 0 0) =
  Rsqr (C_mod l) * Re ((conjugate_transpose vi *m
                          (RtoC_mat A *m vi)) 0 0).
Proof.
intros. rewrite !mxE. rewrite -!eq_big_Re_C.
rewrite big_distrr //=. apply eq_big. by [].
intros. rewrite !mxE. rewrite !big_distrr //=.
rewrite -!eq_big_Re_C. rewrite big_distrr //=.
apply eq_big. by []. intros. rewrite !mxE //=.
assert ((((l * vi i 0)^*)%C * ((A i i0 +i* 0)%C * (l * vi i0 0))) =
         ( ((l * vi i 0)^*)%C * (l * vi i0 0)) * (A i i0 +i* 0)%C).
{ rewrite mulrC. rewrite -[LHS]mulrA. rewrite [in RHS]mulrC.
  assert ((l * vi i0 0 * ((l * vi i 0)^*)%C) =
            (((l * vi i 0)^*)%C * (l * vi i0 0))).
  { by rewrite mulrC. } by rewrite H1.
} rewrite H1. rewrite [in LHS]mulrC. rewrite Re_prod.
assert (((vi i 0)^*)%C * ((A i i0 +i* 0)%C * vi i0 0) =
          ( ((vi i 0)^*)%C * vi i0 0) * (A i i0 +i* 0)%C).
{ rewrite [in LHS]mulrC. rewrite -[in LHS]mulrA. rewrite [in RHS]mulrC.
  assert ((vi i0 0 * ((vi i 0)^*)%C) = (((vi i 0)^*)%C * vi i0 0)).
  { by rewrite mulrC. } by rewrite H2.
} rewrite H2.
assert (Re (((vi i 0)^*)%C * vi i0 0 * (A i i0 +i* 0)%C) =
        Re ((A i i0 +i* 0)%C * (((vi i 0)^*)%C * vi i0 0))).
{ by rewrite mulrC. } rewrite H3.
rewrite Re_prod.
assert ((((l * vi i 0)^*)%C * (l * vi i0 0)) =
         (l * vi i0 0)  * ((l * vi i 0)^*)%C).
{ by rewrite mulrC. } rewrite H4.
rewrite Cconj_prod.
assert ((l * vi i0 0 * ((l^*)%C * ((vi i 0)^*)%C)) =
        (l * ((l^*)%C)) * (((vi i 0)^*)%C * vi i0 0)).
{ assert (vi i0 0 * ((l^*)%C * ((vi i 0)^*)%C) =
          (l^*)%C * (((vi i 0)^*)%C * vi i0 0)).
  { rewrite [in LHS]mulrC. by rewrite mulrA. }
  rewrite -mulrA. rewrite H5. by rewrite mulrA.
} rewrite H5. rewrite conj_mag.
rewrite Re_prod //=. rewrite [in RHS]mulrC.
rewrite -[in RHS]mulrA.
assert (((C_mod l)² * Re (((vi i 0)^*)%C * vi i0 0)) =
            (Re (((vi i 0)^*)%C * vi i0 0) * (C_mod l)²)).
{ by rewrite mulrC. } by rewrite H6.
Qed.

Lemma Mopp_mult_r_complex:
  forall (m n p:nat) (A: 'M[complex R]_(m.+1,n.+1)) (B: 'M[complex R]_(n.+1,p.+1)),
   oppmx (mulmx A B) = mulmx A (oppmx B).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite -mulrN.
Qed.

Lemma Mopp_mult_l_complex:
  forall (m n p:nat) (A: 'M[complex R]_(m.+1,n.+1)) (B: 'M[complex R]_(n.+1,p.+1)),
   oppmx (mulmx A B) = mulmx (oppmx A) B.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
rewrite -sumrN. apply eq_big. by []. intros. rewrite mxE.
by rewrite mulNr.
Qed.

Lemma Mopp_opp_complex :
  forall (m n:nat) (A: 'M[complex R]_(m.+1,n.+1)), oppmx (oppmx A) = A.
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE. apply opprK.
Qed.


Lemma A_A1_A2_split: forall (n:nat) (A: 'M[R]_n.+1),
  A = addmx (A1 A) (A2 A).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
assert ((y<=x)%N \/ (y>=x)%N). { apply /orP. apply leq_total. } destruct H.
+ assert (y <=? x = true).
  { apply leb_correct. apply /ssrnat.leP. apply H. }
  rewrite H0. rewrite leq_gtF. by rewrite addr0 //=. by [].
+ assert ( x == y \/ (x<y)%N). { apply /orP. rewrite -leq_eqVlt. apply H. }
  destruct H0.
  - assert (x= y). { by apply /eqP. } rewrite -H1.
    assert ((x <=? x)%N = true). { apply leb_correct. lia. } rewrite H2.
    assert ((x < x)%N = false).  { apply ltnn. } rewrite H3.
    by rewrite addr0.
  - assert ((y <=? x)%N = false). { apply leb_correct_conv. apply /ssrnat.ltP. apply H0. }
    rewrite H1. rewrite H0. by rewrite add0r.
Qed.


Lemma A1_is_triangular: forall (n:nat) (A: 'M[R]_n.+1),
  is_trig_mx (A1 A).
Proof.
intros. rewrite /is_trig_mx.
apply /forallP. intros.
apply /forallP. intros.
rewrite !mxE.
assert ((x0 <= x)%coq_nat \/ (x < x0)%coq_nat).
{ lia. } destruct H.
+ assert ( (x0 <= x)%N). { by apply /ssrnat.leP. }
  assert ((x < x0)%N = false). { by apply leq_gtF. }
  by rewrite H1.
+ assert ((x < x0)%N). { by apply /ssrnat.ltP. }
  rewrite H0. simpl.
  assert (x0 <=? x = false).
  { apply leb_correct_conv. apply /ssrnat.ltP. apply H0. }
  by rewrite H1.
Qed.


Lemma A1_prod: forall (n:nat) (F : 'I_n.+1 -> R),
  (forall i, 0 < F i) ->
  (0 < \big[ *%R/1]_(i < succn n) F i)%Re.
Proof.
intros. induction n.
+ rewrite big_ord_recr //= big_ord0 mul1r. by apply /RltP.
+ rewrite big_ord_recr //=. rewrite -RmultE.
  apply Rmult_lt_0_compat.
  - by apply IHn.
  - by apply /RltP.
Qed.

Lemma A1_is_invertible:
  forall (n:nat) (A: 'M[R]_n.+1),
  (forall i:'I_n.+1,  A i i > 0) ->
  A1 A \in unitmx.
Proof.
intros.
rewrite unitmxE.
assert (\det (A1 A) = \prod_(i < n.+1) ((A1 A) i i)).
{ apply det_trig, A1_is_triangular. }
rewrite H0.
rewrite unitrE. apply /eqP.
assert (forall i, A1 A i i = A i i).
{ intros. rewrite !mxE.
  assert (i <=? i = true). { apply leb_correct. lia. }
  by rewrite H1.
}
rewrite -RdivE.
+ apply Rinv_r.
  assert ( (0 < \big[ *%R/1]_(i < succn n) A1 A i i )%Re ->
            (\big[ *%R/1]_(i < succn n) A1 A i i)%Re <> 0%Re).
  { nra. } apply H2.  apply A1_prod.
  intros. by rewrite H1.
+ apply /eqP.
  assert ( (0 < \big[ *%R/1]_(i < succn n) A1 A i i )%Re ->
            (\big[ *%R/1]_(i < succn n) A1 A i i)%Re <> 0%Re).
  { nra. } apply H2.
  apply A1_prod.
  intros. by rewrite H1.
Qed.


(** Proof of the Reich theorem for the Gauss_seidel iteration **)
Theorem Reich_sufficiency: forall (n:nat) (A: 'M[R]_n.+1),
  (forall i:'I_n.+1,  A i i > 0) ->
  (forall i j:'I_n.+1,   A i j = A j i) ->
  is_positive_definite A ->
    (let S:= oppmx (mulmx (RtoC_mat (invmx (A1 A))) (RtoC_mat (A2 A))) in
      (forall i: 'I_n.+1, C_mod (lambda S i) < 1)).
Proof.
intros.

assert (A= addmx (A1 A) (A2 A)). { by apply A_A1_A2_split. }
assert (A1 A \in unitmx). { by apply A1_is_invertible. }

(*** Working with the ith characteristic pair  **)

assert (forall i: 'I_n.+1,
          @eigenvalue (complex_fieldType _) n.+1 S (lambda S i)).
{ apply Jordan_ii_is_eigen. }

remember (lambda S i) as li.
assert ( exists v: 'cV_n.+1, (mulmx S v = (lambda S i) *: v) /\ (v != 0)).
{ specialize (H4 i). by apply right_eigen_vector_exists. }
destruct H5 as [vi H5].
remember (RtoC_mat ((A1 A))) as A1_C.

(** equation (2) **)

assert (mulmx (mulmx (- conjugate_transpose vi) A1_C) (mulmx S vi)=
           mulmx (mulmx (- conjugate_transpose vi) A1_C) (scal_vec_C li vi)).
{ apply matrix_eq. rewrite -scal_vec_mathcomp_compat_col. rewrite Heqli. apply H5. }


(** simpligying equation (2) **)
assert (mulmx (mulmx (- conjugate_transpose vi) A1_C) (mulmx S vi)=
           mulmx (mulmx (mulmx (- conjugate_transpose vi) A1_C) S) vi).
{ apply mulmxA. } rewrite H7 in H6.

assert (mulmx (mulmx (- conjugate_transpose vi) A1_C) S =
            mulmx (conjugate_transpose vi)  (mulmx (-A1_C) S)).
{ symmetry. rewrite -Mopp_mult_l_complex -Mopp_mult_r_complex.
  rewrite -![in RHS]Mopp_mult_l_complex. by rewrite mulmxA.
} rewrite H8 in H6.
clear H7 H8.

assert (mulmx (-A1_C) S = RtoC_mat (A2 A)).
{ unfold S. rewrite Mopp_mult_l_complex.
  assert (mulmx (-A1_C) ((mulmx (oppmx (RtoC_mat (invmx (A1 A)))) (RtoC_mat (A2 A))))=
           mulmx (mulmx (-A1_C) (oppmx (RtoC_mat ((invmx (A1 A)))))) (RtoC_mat (A2 A))).
  { apply mulmxA. } rewrite H7. clear H7.
  rewrite HeqA1_C. rewrite -Mopp_mult_r_complex -!Mopp_mult_l_complex .
  rewrite Mopp_opp_complex. rewrite RtoC_mat_prod.
  assert (mulmx (A1 A) (invmx (A1 A)) = 1%:M /\ mulmx (invmx (A1 A)) (A1 A) = 1%:M).
  { by apply inverse_A. } destruct H7. rewrite H7.
  rewrite RtoC_mat_prod. by rewrite mul1mx.
} rewrite H7 in H6.

(* Work on the RHS of (2) *)
assert (mulmx (mulmx (- conjugate_transpose vi) A1_C) (scal_vec_C li vi)=
            scal_vec_C (-li)%C (mulmx (mulmx (conjugate_transpose vi) A1_C) vi)).
{ rewrite /conjugate_transpose /scal_vec_C /transpose_C /conjugate.
  apply matrixP. unfold eqrel. intros. rewrite !mxE. rewrite big_scal.
  apply eq_big. by []. intros. rewrite !mxE.
  rewrite -mulrC -!mulrA. rewrite !big_distrr //=. rewrite big_distrl //=.
  rewrite big_distrr //=. apply eq_big. by [].
  intros. rewrite !mxE. rewrite !mulNr. rewrite !mulrN.
  assert ((vi i0 0 * (((vi i1 x)^*)%C * A1_C i1 i0))%C =
          (((vi i1 x)^*)%C * A1_C i1 i0 * vi i0 0)%C).
  { by rewrite mulrC. } by rewrite H10.
} rewrite H8 in H6. clear H8.

(* Working on (3) *)
assert (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi=
          scal_vec_C (RtoC 1- li)%C
          (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat ((A1 A)))) vi)).
{ have H9: conjugate_transpose vi *m RtoC_mat A *m vi =
            conjugate_transpose vi *m RtoC_mat (addmx (A1 A) (A2 A)) *m vi.
  rewrite <-H2. reflexivity. rewrite H9. clear H9.
  rewrite RtoC_mat_add. rewrite mulmxDr mulmxDl. rewrite H6. rewrite -scal_vec_add_xy.
  have H9: conjugate_transpose vi *m RtoC_mat ((A1 A)) *m vi = (scal_vec_C (RtoC 1)
              (conjugate_transpose vi *m RtoC_mat ((A1 A)) *m vi)).
  { apply matrixP. unfold eqrel. intros. rewrite !mxE.
    assert (y= 0). { apply ord1. } rewrite H8 /RtoC. by rewrite mul1r.
  } rewrite H9. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. by rewrite !mul1r HeqA1_C.
}

(** (1+li)<>0 **)
assert ( (RtoC 1-li)%C <> 0%C).
{ destruct H5.
  assert (forall x: 'cV[complex R]_n.+1,  x != 0 ->
        scal_of_mat0 (mulmx (mulmx (conjugate_transpose x) (RtoC_mat A)) x) <> 0%C).
  { unfold is_positive_definite in H1. intros.
    specialize (H1 x H10). rewrite /scal_of_mat0.
    assert ((conjugate_transpose x *m RtoC_mat A *m x) 0 0 =
            (Re ((conjugate_transpose x *m RtoC_mat A *m x) 0 0) +i*
              Im ((conjugate_transpose x *m RtoC_mat A *m x) 0 0))%C).
    { apply C_destruct. } rewrite H11.
    apply /eqP. rewrite eq_complex //=. apply /nandP. left.
    apply /eqP. apply Rgt_not_eq. apply Rlt_gt. apply /RltP.
    by rewrite -mulmxA.
  } specialize (H10 vi H9).
  assert ( ((RtoC 1 - li)%C * (scal_of_mat0
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)))%C <> 0%C <->
              (RtoC 1 - li)%C <> 0%C /\ (scal_of_mat0
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)) <> 0%C).
  { apply prod_not_zero. } destruct H11.
  assert (scal_of_mat0 (scal_vec_C (RtoC 1 - li)%C  (mulmx
           (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi) )=
            ((RtoC 1 - li)%C *
                   (scal_of_mat0
                     (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)))%C).
  { apply scal_conv_scal_vec. } rewrite <-H13 in H11. rewrite <-H8 in H11.
  specialize (H11 H10). destruct H11. apply H11.
}

(** conjugate transpose, LHS and RHS: (4) to (5) **)
assert (scal_vec_C (RtoC 1 - li)%C (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)=
              scal_mat_C (RtoC 1 - li)%C (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi)).
{ symmetry. apply scal_mat_to_vec. } rewrite H10 in H8. clear H10.
assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
            conjugate_transpose (scal_mat_C (RtoC 1 - li)%C  (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat (A1 A))) vi))).
{ by rewrite H8. }
(*LHS*)
assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
              mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi).
{ assert (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)=
                mulmx (conjugate_transpose vi)
                  (conjugate_transpose (mulmx (conjugate_transpose vi) (RtoC_mat A)))).
  { apply (conj_matrix_mul (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi). }
  rewrite H11.
  assert (conjugate_transpose (mulmx (conjugate_transpose vi) (RtoC_mat A))=
               mulmx (conjugate_transpose (RtoC_mat A)) (conjugate_transpose (conjugate_transpose vi))).
  { apply conj_matrix_mul. } rewrite H12.
  assert (conjugate_transpose (conjugate_transpose vi) = vi). { apply conj_of_conj. } rewrite H13.
  assert (conjugate_transpose (RtoC_mat A) = RtoC_mat A). { apply conj_transpose_A.  apply H0. }
  rewrite H14. apply mulmxA.
} rewrite H11 in H10.


(*RHS*)
assert (conjugate_transpose (scal_mat_C (RtoC 1 - li)%C (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi)) = scal_mat_C (conjc (RtoC 1 - li)%C)
              (conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi))).
{ apply conj_scal_mat_mul. } rewrite H12 in H10.
assert ((conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi))= mulmx (mulmx (conjugate_transpose vi)
              (transpose_C (RtoC_mat (A1 A)))) vi).
{ assert ((conjugate_transpose (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))) vi)) = mulmx (conjugate_transpose vi)
                  (conjugate_transpose (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A))))).
  { apply conj_matrix_mul. }  rewrite H13.
  assert ((conjugate_transpose (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A1 A)))) = mulmx (conjugate_transpose (RtoC_mat (A1 A)))
                (conjugate_transpose (conjugate_transpose vi))).
  { apply conj_matrix_mul. } rewrite H14.
  assert (conjugate_transpose (conjugate_transpose vi) = vi).
  { apply conj_of_conj. } rewrite H15.
  assert ((conjugate_transpose (RtoC_mat (A1 A))) = transpose_C (RtoC_mat (A1 A))).
  { apply conj_transpose_A1. } rewrite H16. by rewrite mulmxA.
} rewrite H13 in H10. clear H11 H12 H13.
assert ((conjc (RtoC 1 - li)%C = (RtoC 1 - conjc li)%C)).
{ assert ( conjc (RtoC 1)= (RtoC 1)).
  { rewrite /RtoC /conjc. apply /eqP. rewrite eq_complex //=.
    apply /andP. split.
    + by apply /eqP.
    + apply /eqP. by rewrite oppr0.
  } rewrite Cconj_add H11.
  assert (conjc (-li) = - conjc li).
  { assert (li = (Re li +i* Im li)%C). { by rewrite -C_destruct. }
    rewrite H12. by simpc.
  } by rewrite H12.
} rewrite H11 in H10.
assert (scal_mat_C (RtoC 1 - conjc li)%C
            (mulmx
            (mulmx (conjugate_transpose vi)
              (transpose_C (RtoC_mat (A1 A)))) vi) = scal_vec_C (RtoC 1 - conjc li)%C (mulmx
            (mulmx (conjugate_transpose vi)
              (transpose_C (RtoC_mat (A1 A)))) vi)).
{ apply scal_mat_to_vec. } rewrite H12 in H10. clear H12.

(** Working on (7) **)
assert (transpose_C (RtoC_mat (A1 A)) = addmx (RtoC_mat (diag_A A)) (RtoC_mat (A2 A))).
{ apply A1_tr_split_C. apply H0. }
rewrite H12 in H10.
assert (mulmx (conjugate_transpose vi) (addmx (RtoC_mat (diag_A A)) (RtoC_mat (A2 A))) =
            addmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A)))
                  (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A)))).
{ by rewrite mulmxDr. }
rewrite H13 in H10.
assert (mulmx (addmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A)))
                          (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A)))) vi =
             addmx (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)
                   (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (A2 A))) vi)).
{ by rewrite mulmxDl. } rewrite H14 in H10.

assert (scal_vec_C (RtoC 1 - conjc li)%C (addmx (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (diag_A A))) vi)  (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A2 A))) vi)) = addmx (scal_vec_C (RtoC 1 - conjc li)%C
                (mulmx (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi))
               (scal_vec_C (RtoC 1 - conjc li)%C (mulmx (mulmx (conjugate_transpose vi)
                 (RtoC_mat (A2 A))) vi))).
{ apply matrixP. unfold eqrel. intros. by rewrite !mxE mulrDr.
} rewrite H15 in H10. clear H13 H14 H15.
rewrite H6 in H10.
assert ((scal_vec_C (RtoC 1 - conjc li)%C (scal_vec_C (-li) (mulmx
                 (mulmx (conjugate_transpose vi) A1_C) vi))) = scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                (mulmx (mulmx (conjugate_transpose vi) A1_C) vi)).
{ apply scal_of_scal_vec. } rewrite H13 in H10. clear H13.

(** Working on (8) **)
assert ( mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi=
              scal_vec_C (RtoC 1) (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)).
{ apply matrixP. unfold eqrel. intros. rewrite !mxE. rewrite mul1r.
  assert (y= 0). { apply ord1. } by rewrite H13.
}
assert (scal_vec_C (RtoC 1)
        (mulmx
           (mulmx (conjugate_transpose vi)
              (RtoC_mat A)) vi)= scal_vec_C ((RtoC 1- li)* (invc (RtoC 1- li)))%C
        (mulmx
           (mulmx (conjugate_transpose vi)
              (RtoC_mat A)) vi)).
{ assert (((RtoC 1- li)* (invc (RtoC 1- li)))%C = RtoC 1).
  { rewrite mulrC. apply mulVc. by apply /eqP. (* 1+ lj <> 0 *) }
  by rewrite H14.
} rewrite H14 in H13. clear H14.
assert ( scal_vec_C ((RtoC 1 - li) * invc (RtoC 1 - li))%C (mulmx (mulmx (conjugate_transpose vi)
              (RtoC_mat A)) vi) = scal_vec_C (RtoC 1-li)%C (scal_vec_C (invc (RtoC 1-li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ symmetry. apply scal_of_scal_vec. } rewrite H14 in H13. clear H14.
assert (scal_vec_C (invc (RtoC 1 - li))%C (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi) =
                mulmx (mulmx (conjugate_transpose vi) A1_C) vi).
{ apply (@scal_vec_eq 0%N (RtoC 1-li)%C (scal_vec_C (invc (RtoC 1 - li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
              (mulmx (mulmx (conjugate_transpose vi) A1_C) vi) H9).
  rewrite <-H13. rewrite HeqA1_C. rewrite H8. apply matrixP. unfold eqrel. intros.
  rewrite !mxE. assert (y= 0). { apply ord1. } by rewrite H14.
}
assert (scal_vec_C (RtoC 1 - conjc li)%C  (mulmx  (mulmx (conjugate_transpose vi)
                 (RtoC_mat (diag_A A))) vi) = scal_vec_C ((RtoC 1 - conjc li) * ((RtoC 1- li)* (invc (RtoC 1-li))))%C
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)).
{ assert (((RtoC 1-li)* (invc (RtoC 1-li)))%C = RtoC 1).
  { rewrite mulrC. apply mulVc. by apply /eqP. } rewrite H15.
  assert (((RtoC 1 - conjc li) * RtoC 1)%C = (RtoC 1 - conjc li)%C). { apply mulr1. }
  by rewrite H16.
}
assert (((RtoC 1 - conjc li) * ((RtoC 1 - li) * invc (RtoC 1 - li)))%C = ((invc (RtoC 1-li))* ((RtoC 1 - conjc li)*(RtoC 1-li)))%C).
{ assert(((invc (RtoC 1-li))* ((RtoC 1- conjc li)*(RtoC 1-li)))%C = (((RtoC 1- conjc li)*(RtoC 1-li)) * (invc (RtoC 1-li)))%C).
  { apply mulrC. } rewrite H16. apply mulrA.
} rewrite H16 in H15. clear H16.
assert (scal_vec_C (invc (RtoC 1 - li) * ((RtoC 1 - conjc li) * (RtoC 1 - li)))%C (mulmx
              (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi) = scal_vec_C (invc (RtoC 1 - li))%C
                (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C (mulmx
              (mulmx (conjugate_transpose vi)  (RtoC_mat (diag_A A))) vi))).
{ symmetry. apply scal_of_scal_vec. } rewrite H16 in H15. clear H16.
assert (scal_vec_C (RtoC 1 - li)%C (scal_vec_C (invc (RtoC 1 - li))%C (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) =
            scal_vec_C (invc (RtoC 1 - li))%C (scal_vec_C (RtoC 1 - li)%C (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ apply scal_vec_C_comm. } rewrite H16 in H13. clear H16.
assert ( scal_vec_C (invc(RtoC 1 - li))%C (scal_vec_C (RtoC 1 - li)%C  (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi)) = addmx (scal_vec_C (invc (RtoC 1 - li))%C (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)))
              ( scal_vec_C ((RtoC 1 - conjc li) * (-li))%C  (scal_vec_C (invc (RtoC 1 - li))%C  (mulmx
                (mulmx (conjugate_transpose vi)  (RtoC_mat A)) vi)))).
{ rewrite <- H15.  rewrite <- H13.  rewrite H14. apply H10. }
assert ((scal_vec_C ((RtoC 1 - conjc li) * (-li))%C  (scal_vec_C (invc (RtoC 1 - li))%C
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))) =
              (scal_vec_C (invc (RtoC 1 - li))%C  (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))).
{ apply scal_vec_C_comm. } rewrite H17 in H16. clear H17.
assert ( addmx
              (scal_vec_C (invc (RtoC 1 - li))%C
                (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C
                 (mulmx
                    (mulmx (conjugate_transpose vi)
                        (RtoC_mat (diag_A A))) vi)))
              (scal_vec_C (invc (RtoC 1 - li))%C
                (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                  (mulmx
                    (mulmx (conjugate_transpose vi)
                        (RtoC_mat A)) vi))) = scal_vec_C (invc (RtoC 1 - li))%C (addmx
                (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C
                 (mulmx
                    (mulmx (conjugate_transpose vi)
                        (RtoC_mat (diag_A A))) vi)) (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                  (mulmx
                    (mulmx (conjugate_transpose vi)
                        (RtoC_mat A)) vi)))).
{ apply scal_vec_add. } rewrite H17 in H16. clear H17.
assert ((scal_vec_C (RtoC 1 - li)%C  (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) =
           addmx
           (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C
              (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
           (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
              (mulmx  (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))).
{ apply scal_vec_eq with (invc (RtoC 1 - li))%C. apply Cinv_not_0.
  apply H9. apply H16.
}
assert (scal_vec_C (RtoC 1 - li)%C  (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi) =
              addmx (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C  (mulmx
                        (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
                     (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) ->
              addmx (scal_vec_C (RtoC 1 - li)%C  (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
                    (oppmx (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))) =
              addmx (addmx (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C  (mulmx
                        (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
                     (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))
                    (oppmx (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))).
{ apply Mplus_add_mat_eq. }  specialize (H18 H17).
assert ( addmx (addmx (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C  (mulmx
                        (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
                     (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))
                    (oppmx (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))=
            addmx (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C  (mulmx
                        (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))
                  (addmx (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
                      (oppmx (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                        (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))))).
{ symmetry. apply addmxA. } rewrite H19 in H18. clear H19.
assert ((addmx (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                      (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))
                      (oppmx (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C
                        (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)))) = 0).
{ apply Mplus_opp_r_C. }  rewrite H19 in H18. clear H19.
assert (addmx (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C
                    (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi)) 0=
                (scal_vec_C ((RtoC 1 - conjc li) * (RtoC 1 - li))%C
                    (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat (diag_A A))) vi))).
{ apply Mplus_zero_r_C. } rewrite H19 in H18. clear H19.
assert (oppmx (scal_vec_C ((RtoC 1 - conjc li) * (-li))%C (mulmx
                 (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) =
              scal_vec_C  (-((RtoC 1 - conjc li) * (-li)))%C (mulmx
                 (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)).
{ apply scal_vec_C_Mopp. } rewrite H19 in H18. clear H19.
assert (addmx
        (scal_vec_C (RtoC 1 - li)%C
           (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi))
        (scal_vec_C (- ((RtoC 1 - conjc li) * (-li)))%C
           (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi)) = scal_vec_C ((RtoC 1 - li) + (- ((RtoC 1 - conjc li) * (-li))))%C  (mulmx
              (mulmx (conjugate_transpose vi) (RtoC_mat A))  vi)).
{ apply scal_vec_add_xy. } rewrite H19 in H18. clear H19.
assert (((RtoC 1 - li) + (- ((RtoC 1 - conjc (li)) * (-li))))%C = (RtoC 1 - (conjc li * li))%C).
{ rewrite mulrDl mul1r -addrA.
  assert ((- li - (- li + - (li^*)%C * - li)) = - (((li)^*)%C * (li))).
  { by rewrite opprD addrA addrC addrN addr0 mulNr opprK mulrN. }
  by rewrite H19 //= mulNr.
} rewrite H19 in H18. clear H19.

(** Simplifying the LHS of (8): Conj li * li = (Cmod li)^2  **)

assert ((RtoC 1 - (conjc li * li))%C = (RtoC 1- RtoC (Rsqr (C_mod li)))%C).
{ assert ((conjc li * li)%C= RtoC (Rsqr (C_mod li))). { apply conj_prod. }
  by rewrite H19.
} rewrite H19 in H18.

assert ( (RtoC 1 - RtoC (C_mod li)²)%C = RtoC (1- Rsqr (C_mod li))).
{ rewrite /RtoC. apply /eqP. rewrite eq_complex //=. apply /andP.
  split.
  + by apply /eqP.
  + apply /eqP. by rewrite subr0.
} rewrite H20 in H18.


assert (((RtoC 1 - conjc li) * (RtoC 1 - li))%C = RtoC (Rsqr (C_mod (RtoC 1 - li)%C))).
{ assert ((RtoC 1 - conjc li)%C = conjc (RtoC 1 -  li)%C).
  { assert (conjc (RtoC 1) = RtoC 1).
    { rewrite /conjc /RtoC. apply /eqP. rewrite eq_complex //=. apply /andP.
    split. by apply /eqP. rewrite oppr0. by apply /eqP.
    } rewrite Cconj_add H21.
    assert (- (li^*)%C = ((- li)^*)%C).
    { assert (li = (Re li +i* Im li)%C). { by rewrite -C_destruct. }
      rewrite H22. by simpc.
    } by rewrite H22.
  } rewrite H21. apply conj_prod.
} rewrite H21 in H18.

  unfold is_positive_definite in H1. destruct H5.
  specialize (H1 vi H22).
  assert (is_positive_definite (diag_A A)).
  { apply is_positive_definite_diag. auto. }



  assert (scal_of_mat0 (scal_vec_C (RtoC (1 - (C_mod li)²))
            (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi)) =
             scal_of_mat0 (scal_vec_C (RtoC (C_mod (RtoC 1 - li)%C)²)
              (mulmx
                 (mulmx (conjugate_transpose vi)
                    (RtoC_mat (diag_A A))) vi))).
  { unfold scal_of_mat0. by rewrite H18.  }

  assert (scal_of_mat0
            (scal_vec_C (RtoC (1 - (C_mod li)²))
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi)) = ((RtoC (1 - (C_mod li)²)) *
                    scal_of_mat0 (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C).
  { apply scal_conv_scal_vec. } rewrite H25 in H24. clear H25.

  assert (scal_of_mat0
            (scal_vec_C (RtoC (C_mod (RtoC 1 - li)%C)²)
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)) = ((RtoC (C_mod (RtoC 1 - li)%C)²) *
                scal_of_mat0 (mulmx  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C).
  { apply scal_conv_scal_vec. } rewrite H25 in H24. clear H25.

  assert (((RtoC (1 - (C_mod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C =
            ((RtoC (C_mod (RtoC 1 - li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C ->
            Re (((RtoC (1 - (C_mod li)²)%R) *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi))%C) =

            Re (((RtoC (C_mod (RtoC 1 - li))²) *
             scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))%C)).
  { apply Re_eq. } specialize (H25 H24).

  assert (Re
            (RtoC (1 - (C_mod li)²)%R *
             scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi))%C = Re (RtoC (1 - (C_mod li)²)%R) * Re (scal_of_mat0
               (mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
                  vi))).
  { apply Re_prod. } rewrite H26 in H25. clear H26.

  assert (Re
            ((RtoC (C_mod (RtoC 1 - li)%C)²) *
             (scal_of_mat0
               (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)))%C = Rmult (Re (RtoC (C_mod (RtoC 1 - li)%C)²))
                (Re (scal_of_mat0 (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi)))).
  { apply Re_prod. } rewrite H26 in H25. clear H26. unfold scal_of_mat0 in H25.

  unfold is_positive_definite in H23.
  specialize (H23 vi H22).

  assert (Rmult (Re (RtoC (C_mod (RtoC 1 - li)%C)²))
                (Re (scal_of_mat0 (mulmx
                  (mulmx (conjugate_transpose vi)
                     (RtoC_mat (diag_A A))) vi))) >0%Re).
  { apply /RltbP. apply Rmult_gt_0_compat.
    unfold RtoC. simpl. apply Rlt_gt. apply Rsqr_pos_lt.
    assert ( Rlt 0%Re (C_mod ((1 +i* 0)%C - li)%C) -> C_mod ((1 +i* 0)%C-  li)%C <> 0%Re). { nra. }
    apply H26. apply /RltP. apply C_mod_gt_0. apply H9. apply /RltbP. rewrite mulmxA in H23. apply H23.
  }  unfold scal_of_mat0 in H26. rewrite <-H25 in H26. apply /RltbP.
  apply Rsqr_incrst_0.
  - assert ( Rsqr 1 = 1%Re). { apply Rsqr_1. } rewrite H27. apply Rplus_lt_reg_r with (-1).
    assert ((1 + -1)%Re= 0%Re). { nra. }  rewrite H28.
    assert (((C_mod li)² + -1)%Re = ((C_mod li)² -1)%Re). { nra. } rewrite H29.
    apply Ropp_lt_cancel. assert ((-0)%Re= 0%Re).  { nra. } rewrite H30.
    assert ((- ((C_mod li)² - 1))%Re = (1- (C_mod li)²)%Re). { nra. } rewrite H31.
    assert (Re (RtoC (1 - (C_mod li)²)) = (1 - (C_mod li)²)%Re).
    { unfold RtoC. simpl. reflexivity. } rewrite <-H32.
    apply Rmult_lt_reg_r with (Re
        ((mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A))
              vi) 0 0)).
    * rewrite mulmxA in H1.  apply /RltbP. apply H1.
    * assert ( 0 *
                  Re
                    ((mulmx (mulmx (conjugate_transpose vi) (RtoC_mat A)) vi) 0 0)= 0%Re).
      { by rewrite mul0r. } apply /RltbP. rewrite RmultE. rewrite H33. apply H26.
  - apply C_mod_ge_0.
  - apply Rlt_le. apply Rlt_0_1.
Qed.


Lemma RtoC_mat_oppmx :
  forall (n:nat) (A: 'M[R]_n.+1),
  RtoC_mat (oppmx A) = oppmx (RtoC_mat A).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite !mxE.
apply /eqP. rewrite eq_complex. apply /andP.
split.
+ apply /eqP. by rewrite //=.
+ apply /eqP. by rewrite //= oppr0.
Qed.

Lemma big_minus (n:nat) (F : 'I_n.+1 -> (complex R)):
  - (\big[+%R/0]_(j < n.+1) (F j)) = (\big[+%R/0]_(j < n.+1) (-(F j))).
Proof.
induction n.
+ rewrite !big_ord_recr //= !big_ord0. by rewrite add0r sub0r.
+ rewrite big_ord_recr //=. rewrite [in RHS]big_ord_recr //=.
  rewrite -IHn. by rewrite opprD.
Qed.


Lemma Mopp_vec_mult_r:
  forall (n:nat) (A: 'M[complex R]_n.+1) (v: 'rV[complex R]_n.+1),
  v *m oppmx A = oppmx (v *m A).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. rewrite big_minus.
apply eq_big. by [].
intros. rewrite !mxE. by rewrite mulrN.
Qed.

Lemma Mopp_opp_vec:
  forall (n:nat) (A: 'M[complex R]_n.+1) (v: 'rV[complex R]_n.+1),
  v *m A = oppmx (oppmx (v *m A)).
Proof.
intros. apply matrixP. unfold eqrel.
intros. rewrite !mxE. by rewrite opprK.
Qed.

Lemma eigenvalue_oppmx:
  forall (n:nat) (A: 'M[complex R]_n.+1) (l : complex R),
  @eigenvalue (complex_fieldType _) n.+1 A l <->
  @eigenvalue (complex_fieldType _) n.+1 (oppmx A) (-l).
Proof.
intros. split.
+ intros.
  assert (exists2 v : 'rV_n.+1, v *m A = l *: v & v != 0).
  { by apply /eigenvalueP. } destruct H0 as [v H0].
  apply /eigenvalueP. exists v.
  - rewrite Mopp_vec_mult_r H0. apply matrixP. unfold eqrel.
    intros. rewrite !mxE. by rewrite -mulNr.
  - by [].
+ intros.
  assert (exists2 v : 'rV_n.+1, v *m (oppmx A) = -l *: v & v != 0).
  { by apply /eigenvalueP. } destruct H0 as [v H0].
  apply /eigenvalueP. exists v.
  - rewrite Mopp_opp_vec. rewrite -Mopp_vec_mult_r.
    rewrite H0. apply matrixP. unfold eqrel. intros. rewrite !mxE.
    by rewrite mulNr opprK.
  - by [].
Qed.


Theorem Gauss_Seidel_converges:
  forall (n:nat) (A: 'M[R]_n.+1) (b: 'cV[R]_n.+1),
  let x:= (invmx A) *m b in
   A \in unitmx ->
   (forall i : 'I_(succn n), 0 < A i i) ->
   (forall i j : 'I_(succn n), A i j = A j i) ->
   is_positive_definite A ->
    (forall x0: 'cV[R]_n.+1,
        is_lim_seq (fun m:nat => vec_norm (addmx (X_m m.+1 x0 b (A1 A) (A2 A)) (oppmx x))) 0%Re).
Proof.
intros.
apply iter_convergence.
+ by [].
+ by apply A1_is_invertible.
+ apply A_A1_A2_split.
+ intros. rewrite /S_mat. apply /RltP.
  rewrite RtoC_mat_oppmx.
  assert (forall (n:nat) (A: 'M[R]_n.+1),
          (forall i:'I_n.+1,  A i i > 0) ->
          (forall i j:'I_n.+1,   A i j = A j i) ->
          is_positive_definite A ->
            (let S:= oppmx (mulmx (RtoC_mat (invmx (A1 A))) (RtoC_mat (A2 A))) in
              (forall i: 'I_n.+1, C_mod (lambda S i) < 1))).
   { apply Reich_sufficiency. }
  specialize (H3 n A H0 H1).
  assert (A = addmx (A1 A) (A2 A)). { by apply A_A1_A2_split. }
  specialize (H3 H2).
  simpl in H3. rewrite RtoC_mat_prod in H3.
  apply H3.
Qed.


(** Gauss Seidel iteration for a 3 x 3 matrix **)

(** define a tridiagonal system **)
Definition A (n:nat):= \matrix_(i<n.+1, j<n.+1)
   if (i==j :> nat) then 2 else
      (if ((i-j)%N==1%N :>nat) then (-1)%Re else
            (if ((j-i)%N==1%N :>nat) then (-1)%Re else 0)).


(** Positive definiteness of a 3 x 3 matrix **)
Definition Ah (n:nat)(h:R) := \matrix_(i<n.+1,j<n.+1)
    ((1/(h^2)) * ((A n) i j))%Re.

Lemma Ah_pd:
  forall (h:R), (0<h)%Re ->
  is_positive_definite (Ah 2%N h).
Proof.
intros. rewrite /is_positive_definite.
intros. rewrite !mxE.
rewrite !big_ord_recr //= big_ord0 //= add0r.
rewrite !Re_add. rewrite !mxE.
rewrite !big_ord_recr //= !big_ord0 //= !add0r.
rewrite !mxE //=. rewrite !Rmult_1_r.
rewrite !mulrDr !Re_add. rewrite !Rmult_0_r //=.
assert ( (((x
         (widen_ord (leqnSn 2)
            (widen_ord (leqnSn 1) ord_max)) 0)^*)%C *
         (((1 / (h * h) * 2)%Re +i* 0)%C *
          x
            (widen_ord (leqnSn 2)
               (widen_ord (leqnSn 1) ord_max)) 0)) =
         (x
            (widen_ord (leqnSn 2)
               (widen_ord (leqnSn 1) ord_max)) 0 *
          ((x
         (widen_ord (leqnSn 2)
            (widen_ord (leqnSn 1) ord_max)) 0)^*)%C) *
          ((1 / (h * h) * 2)%Re +i* 0)%C).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1.
rewrite conj_mag. rewrite Re_prod //=.
assert ((((x ord_max 0)^*)%C *
            (((1 / (h * h) * 2)%Re +i* 0)%C * x ord_max 0)) =
        (x ord_max 0 * ((x ord_max 0)^*)%C) *
          ((1 / (h * h) * 2)%Re +i* 0)%C).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1.
rewrite conj_mag. rewrite Re_prod //=.
assert ((((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C *
          (((1 / (h * h) * 2)%Re +i* 0)%C *
           x (widen_ord (leqnSn 2) ord_max) 0)) =
         (x (widen_ord (leqnSn 2) ord_max) 0 *
              ((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C) *
         ((1 / (h * h) * 2)%Re +i* 0)%C).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1.
rewrite conj_mag. rewrite Re_prod //=.
assert ((((x ord_max 0)^*)%C *
            (((1 / (h * h) * -1)%Re +i* 0)%C *
             x (widen_ord (leqnSn 2) ord_max) 0)) =
         ((1 / (h * h) * -1)%Re +i* 0)%C *
        ( x (widen_ord (leqnSn 2) ord_max) 0 * ((x ord_max 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ((((x ord_max 0)^*)%C *
            ((0 +i* 0)%C *
             x
               (widen_ord (leqnSn 2)
                  (widen_ord (leqnSn 1) ord_max)) 0)) =
          (0 +i* 0)%C *
          (x
               (widen_ord (leqnSn 2)
                  (widen_ord (leqnSn 1) ord_max)) 0 * ((x ord_max 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ((((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C *
          (((1 / (h * h) * -1)%Re +i* 0)%C * x ord_max 0)) =
          ((1 / (h * h) * -1)%Re +i* 0)%C *
          (x ord_max 0 * ((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ((((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C *
        (((1 / (h * h) * -1)%Re +i* 0)%C *
         x
           (widen_ord (leqnSn 2)
              (widen_ord (leqnSn 1) ord_max)) 0)) =
        ((1 / (h * h) * -1)%Re +i* 0)%C *
        (x
           (widen_ord (leqnSn 2)
              (widen_ord (leqnSn 1) ord_max)) 0 *
          ((x (widen_ord (leqnSn 2) ord_max) 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ( (((x
             (widen_ord (leqnSn 2)
                (widen_ord (leqnSn 1) ord_max)) 0)^*)%C *
         ((0 +i* 0)%C * x ord_max 0)) =
        (0 +i* 0)%C *
        ( x ord_max 0 * ((x
             (widen_ord (leqnSn 2)
                (widen_ord (leqnSn 1) ord_max)) 0)^*)%C )).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
assert ((((x
       (widen_ord (leqnSn 2)
          (widen_ord (leqnSn 1) ord_max)) 0)^*)%C *
         (((1 / (h * h) * -1)%Re +i* 0)%C *
          x (widen_ord (leqnSn 2) ord_max) 0)) =
      ((1 / (h * h) * -1)%Re +i* 0)%C *
      (x (widen_ord (leqnSn 2) ord_max) 0 * ((x
       (widen_ord (leqnSn 2)
          (widen_ord (leqnSn 1) ord_max)) 0)^*)%C)).
{ rewrite mulrC. rewrite -[LHS]mulrA. by rewrite mulrC. }
rewrite H1. clear H1. rewrite Re_prod //=.
remember (x (widen_ord (leqnSn 2)
            (widen_ord (leqnSn 1) ord_max)) 0) as a.
remember (x (widen_ord (leqnSn 2) ord_max) 0) as b.
remember (x ord_max 0) as c. rewrite !mul0r !add0r !addr0.
assert ((C_mod a)² * (1 / (h * h) * 2)%Re =
          ((1 / (h * h))%Re * (2 * (C_mod a)² ))%Re).
{ rewrite -RmultE. nra. } rewrite H1. clear H1.
assert ((1 / (h * h) * -1)%Re * (Re (b * (a^*)%C)) =
          ((1 / (h * h))%Re * (- (Re (b * (a^*)%C))))).
{ rewrite -!RmultE. rewrite -RoppE. nra. }
rewrite H1. clear H1.
assert (((1 / (h * h) * -1)%Re * Re (a * (b^*)%C) =
           ((1 / (h * h))%Re * (- (Re (a * (b^*)%C)))))).
{ rewrite -!RmultE. rewrite -RoppE. nra. }
rewrite H1. clear H1.
assert ((C_mod b)² * (1 / (h * h) * 2)%Re  =
           ((1 / (h * h))%Re * (2 * (C_mod b)² ))%Re).
{ rewrite -RmultE. nra. } rewrite H1. clear H1.

assert ((1 / (h * h) * -1)%Re * Re (c * (b^*)%C) =
           ((1 / (h * h))%Re * (- (Re (c * (b^*)%C))))).
{ rewrite -!RmultE. rewrite -RoppE. nra. }
rewrite H1. clear H1.
assert ((1 / (h * h) * -1)%Re * Re (b * (c^*)%C) =
           ((1 / (h * h))%Re * (- (Re (b * (c^*)%C))))).
{ rewrite -!RmultE. rewrite -RoppE. nra. }
rewrite H1. clear H1.
assert (((C_mod c)² * (1 / (h * h) * 2)%Re) =
         ((1 / (h * h))%Re * (2 * (C_mod c)² ))%Re).
{ rewrite -RmultE. nra. } rewrite H1. clear H1.
assert ((1 / (h * h) * (2 * (C_mod a)²))%Re +
        (1 / (h * h))%Re * - Re (b * (a^*)%C) +
        ((1 / (h * h))%Re * - Re (a * (b^*)%C) +
         (1 / (h * h) * (2 * (C_mod b)²))%Re +
         (1 / (h * h))%Re * - Re (c * (b^*)%C)) +
        ((1 / (h * h))%Re * - Re (b * (c^*)%C) +
         (1 / (h * h) * (2 * (C_mod c)²))%Re) =
        (1 / (h*h))%Re *
          (2* (C_mod a)² - Re (b * (a^*)%C)  -
            Re (a * (b^*)%C) + 2* (C_mod b)² - Re (c * (b^*)%C) -
             Re (b * (c^*)%C) + 2 * (C_mod c)² )).
{ rewrite !mulrDr. by rewrite !addrA. }
rewrite H1. clear H1.
apply /RltP. apply Rmult_lt_0_compat.
+ assert ((1 / (h * h))%Re = (/ (h*h))%Re). { nra. }
  rewrite H1. apply Rinv_0_lt_compat.  by apply Rmult_lt_0_compat.
+ rewrite /C_mod. rewrite !Rsqr_sqrt.
  - assert ( b = (Re b +i* Im b)%C). { by rewrite -C_destruct //=. }
    assert ( a = (Re a +i* Im a)%C). { by rewrite -C_destruct //=. }
    assert ( c = (Re c +i* Im c)%C). { by rewrite -C_destruct //=. }
    rewrite H1 H2 H3 //=. rewrite !mulrDr.
    rewrite -!RminusE -!RplusE -!RmultE -!RoppE.
    assert (exists k, x k 0 != 0).
    { by apply /cV0Pn. } destruct H4 as [k H4].
    assert ((2 * Re a ^+ 2 + 2 * Im a ^+ 2 -
             (Re b * Re a - Im b * - Im a) -
             (Re a * Re b - Im a * - Im b) +
             (2 * Re b ^+ 2 + 2 * Im b ^+ 2) -
             (Re c * Re b - Im c * - Im b) -
             (Re b * Re c - Im b * - Im c) +
             (2 * Re c ^+ 2 + 2 * Im c ^+ 2))%Re =
             ( 2 * Re a ^+ 2 + 2 * Im a ^+ 2 - 2* Re a * Re b -
              2 * Im a * Im b + 2 * Re b ^+ 2 + 2 * Im b ^+ 2 -
              2 * Re b * Re c - 2* Im b * Im c +
              2 * Re c ^+ 2 + 2 * Im c ^+ 2)%Re).
    { nra. } rewrite H5. clear H5.
    assert ((2 * Re a ^+ 2 + 2 * Im a ^+ 2 -
             2 * Re a * Re b - 2 * Im a * Im b +
             2 * Re b ^+ 2 + 2 * Im b ^+ 2 -
             2 * Re b * Re c - 2 * Im b * Im c +
             2 * Re c ^+ 2 + 2 * Im c ^+ 2)%Re =
            ( Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 + Im c ^+ 2 +
             (Re a ^+ 2 - (2 * Re a * Re b) + Re b ^+ 2) +
             (Im a ^+ 2 - (2 * Im a * Im b)  + Im b ^+ 2) +
             (Re b ^+ 2 - (2 * Re b * Re c) + Re c ^+ 2) +
             (Im b ^+ 2 - (2 * Im b * Im c) + Im c ^+ 2))%Re).
    { nra. } rewrite H5. clear H5.
    assert ((2 * Re a * Re b)%Re  = (Re a * Re b *+ 2)).
    { rewrite -[RHS]mulr_natr //=. rewrite [RHS]mulrC.
      rewrite !RmultE. by rewrite mulrA.
    } rewrite H5.  clear H5.
    assert ((2 * Im a * Im b)%Re  = (Im a * Im b *+ 2)).
    { rewrite -[RHS]mulr_natr //=. rewrite [RHS]mulrC.
      rewrite !RmultE. by rewrite mulrA.
    } rewrite H5.  clear H5.
    assert ((2 * Re b * Re c)%Re  = (Re b * Re c *+ 2)).
    { rewrite -[RHS]mulr_natr //=. rewrite [RHS]mulrC.
      rewrite !RmultE. by rewrite mulrA.
    } rewrite H5.  clear H5.
    assert ((2 * Im b * Im c)%Re  = (Im b * Im c *+ 2)).
    { rewrite -[RHS]mulr_natr //=. rewrite [RHS]mulrC.
      rewrite !RmultE. by rewrite mulrA.
    } rewrite H5.  clear H5. rewrite !RplusE.
    rewrite -!sqrrB. rewrite -!RplusE -!RoppE.
    assert ((k = ord_max) \/
             (k = (widen_ord (leqnSn 2)
                  (widen_ord (leqnSn 1) ord_max))) \/
             (k = (widen_ord (leqnSn 2) ord_max))).
    { assert ((k <3)%N). { by []. }
      rewrite leq_eqVlt in H5.
      assert ((k==2%N :> nat) \/ (k < 2)%N). { by apply /orP. }
      destruct H6.
      + left. apply /eqP. by [].
      + rewrite leq_eqVlt in H6.
        assert ((k==1%N :> nat) \/ (k < 1)%N). { by apply /orP. }
        destruct H7.
        - right. right.
          apply /eqP. by [].
        - apply ltnSE in H7.
          rewrite leqn0 in H7. right. left. by apply /eqP.
    }
    destruct H5.
    * rewrite H5 in H4. rewrite -Heqc in H4.
      assert ((Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
               Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
               (Im a + - Im b)%Re ^+ 2 +
               (Re b + - Re c)%Re ^+ 2 +
               (Im b + - Im c)%Re ^+ 2)%Re =
            ((Re c ^+ 2 + Im c ^+ 2) +
            (Re a ^+ 2 + Im a ^+ 2 +
                (Re a + - Re b)%Re ^+ 2 +
               (Im a + - Im b)%Re ^+ 2 +
               (Re b + - Re c)%Re ^+ 2 +
               (Im b + - Im c)%Re ^+ 2))%Re).
      { nra. } rewrite H6.
      apply Rplus_lt_le_0_compat.
      + rewrite H3 in H4. apply complex_not_0 in H4.
        rewrite !expr2. rewrite -!RmultE.
        destruct H4.
        - apply Rplus_lt_le_0_compat.
          * assert (Rsqr (Re c) = (Re c * Re c)%Re).
            { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
            by apply /eqP.
          * assert (Rsqr (Im c) = (Im c * Im c)%Re).
            { by rewrite /Rsqr. } rewrite -H7. nra.
        - apply Rplus_le_lt_0_compat.
          * assert (Rsqr (Re c) = (Re c * Re c)%Re).
            { by rewrite /Rsqr. } rewrite -H7. nra.
          * assert (Rsqr (Im c) = (Im c * Im c)%Re).
            { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
            by apply /eqP.
      + repeat apply Rplus_le_le_0_compat.
        - assert ((Re a ^+ 2)%Re = Rsqr (Re a)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert ((Im a ^+ 2)%Re = Rsqr (Im a)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert (((Re a + - Re b)%Re ^+ 2)%Re = Rsqr ((Re a + - Re b)%Re)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert (((Im a + - Im b)%Re ^+ 2)%Re = Rsqr ((Im a + - Im b)%Re)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
        - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
          { unfold Rsqr. by rewrite expr2 RmultE. }
          rewrite H7. apply Rle_0_sqr .
    * destruct H5.
      ++ rewrite H5 in H4. rewrite -Heqa in H4.
         assert ((Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
               Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
               (Im a + - Im b)%Re ^+ 2 +
               (Re b + - Re c)%Re ^+ 2 +
               (Im b + - Im c)%Re ^+ 2)%Re =
            ((Re a ^+ 2 + Im a ^+ 2) +
            (Re c ^+ 2 + Im c ^+ 2 +
                (Re a + - Re b)%Re ^+ 2 +
               (Im a + - Im b)%Re ^+ 2 +
               (Re b + - Re c)%Re ^+ 2 +
               (Im b + - Im c)%Re ^+ 2))%Re).
        { nra. } rewrite H6.
        apply Rplus_lt_le_0_compat.
        + rewrite H2 in H4. apply complex_not_0 in H4.
          rewrite !expr2. rewrite -!RmultE.
          destruct H4.
          - apply Rplus_lt_le_0_compat.
            * assert (Rsqr (Re a) = (Re a * Re a)%Re).
              { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
              by apply /eqP.
            * assert (Rsqr (Im a) = (Im a * Im a)%Re).
              { by rewrite /Rsqr. } rewrite -H7. nra.
          - apply Rplus_le_lt_0_compat.
            * assert (Rsqr (Re a) = (Re a * Re a)%Re).
              { by rewrite /Rsqr. } rewrite -H7. nra.
            * assert (Rsqr (Im a) = (Im a * Im a)%Re).
              { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
              by apply /eqP.
        + repeat apply Rplus_le_le_0_compat.
          - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert (((Re a + - Re b)%Re ^+ 2)%Re = Rsqr ((Re a + - Re b)%Re)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert (((Im a + - Im b)%Re ^+ 2)%Re = Rsqr ((Im a + - Im b)%Re)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
          - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
            { unfold Rsqr. by rewrite expr2 RmultE. }
            rewrite H7. apply Rle_0_sqr .
        ++ rewrite H5 in H4. rewrite -Heqb in H4.
           rewrite H1 in H4. apply complex_not_0 in H4.
           destruct H4.
           + assert (Re a = Re b \/ (Re a <> Re b)).  { nra. }
             destruct H6.
             - rewrite H6.
               assert ((Re b ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                         Im c ^+ 2 + (Re b + - Re b)%Re ^+ 2 +
                         (Im a + - Im b)%Re ^+ 2 +
                         (Re b + - Re c)%Re ^+ 2 +
                         (Im b + - Im c)%Re ^+ 2)%Re =
                       (Re b ^+ 2 +
                         ( Re c ^+ 2 + Im a ^+ 2 +
                         Im c ^+ 2 + (Re b + - Re b)%Re ^+ 2 +
                         (Im a + - Im b)%Re ^+ 2 +
                         (Re b + - Re c)%Re ^+ 2 +
                         (Im b + - Im c)%Re ^+ 2) )%Re).
               { nra. } rewrite H7. clear H7.
               apply Rplus_lt_le_0_compat.
               * rewrite expr2 -RmultE. assert (Rsqr (Re b) = (Re b * Re b)%Re).
                  { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
                  by apply /eqP.
               * repeat apply Rplus_le_le_0_compat.
                  - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im a ^+ 2)%Re = Rsqr (Im a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re b)%Re ^+ 2)%Re = Rsqr ((Re b + - Re b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im a + - Im b)%Re ^+ 2)%Re = Rsqr ((Im a + - Im b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
            - assert ((Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                       Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
                       (Im a + - Im b)%Re ^+ 2 +
                       (Re b + - Re c)%Re ^+ 2 +
                       (Im b + - Im c)%Re ^+ 2)%Re =
                      ((Re a + - Re b)%Re ^+ 2 +
                      (Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                       Im c ^+ 2 +
                       (Im a + - Im b)%Re ^+ 2 +
                       (Re b + - Re c)%Re ^+ 2 +
                       (Im b + - Im c)%Re ^+ 2))%Re).
              { nra. } rewrite H7. clear H7.
              apply Rplus_lt_le_0_compat.
               * rewrite expr2 -RmultE.
                 assert (Rsqr (Re a + - Re b) = ((Re a + - Re b) * (Re a + - Re b))%Re).
                 { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
                 by apply Rminus_eq_contra.
               * repeat apply Rplus_le_le_0_compat.
                  - assert ((Re a ^+ 2)%Re = Rsqr (Re a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im a ^+ 2)%Re = Rsqr (Im a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im a + - Im b)%Re ^+ 2)%Re = Rsqr ((Im a + - Im b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
             + assert (Im a = Im b \/ (Im a <> Im b)).  { nra. }
             destruct H6.
             - rewrite H6.
               assert ((Re a ^+ 2 + Re c ^+ 2 + Im b ^+ 2 +
                         Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
                         (Im b + - Im b)%Re ^+ 2 +
                         (Re b + - Re c)%Re ^+ 2 +
                         (Im b + - Im c)%Re ^+ 2)%Re =
                       (Im b ^+ 2 +
                         ( Re c ^+ 2 + Re a ^+ 2 +
                         Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
                         (Im b + - Im b)%Re ^+ 2 +
                         (Re b + - Re c)%Re ^+ 2 +
                         (Im b + - Im c)%Re ^+ 2) )%Re).
               { nra. } rewrite H7. clear H7.
               apply Rplus_lt_le_0_compat.
               * rewrite expr2 -RmultE. assert (Rsqr (Im b) = (Im b * Im b)%Re).
                  { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
                  by apply /eqP.
               * repeat apply Rplus_le_le_0_compat.
                  - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Re a ^+ 2)%Re = Rsqr (Re a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re a + - Re b)%Re ^+ 2)%Re = Rsqr ((Re a + - Re b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im b)%Re ^+ 2)%Re = Rsqr ((Im b + - Im b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
            - assert ((Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                       Im c ^+ 2 + (Re a + - Re b)%Re ^+ 2 +
                       (Im a + - Im b)%Re ^+ 2 +
                       (Re b + - Re c)%Re ^+ 2 +
                       (Im b + - Im c)%Re ^+ 2)%Re =
                      ((Im a + - Im b)%Re ^+ 2 +
                      (Re a ^+ 2 + Re c ^+ 2 + Im a ^+ 2 +
                       Im c ^+ 2 +
                       (Re a + - Re b)%Re ^+ 2 +
                       (Re b + - Re c)%Re ^+ 2 +
                       (Im b + - Im c)%Re ^+ 2))%Re).
              { nra. } rewrite H7. clear H7.
              apply Rplus_lt_le_0_compat.
               * rewrite expr2 -RmultE.
                 assert (Rsqr (Im a + - Im b) = ((Im a + - Im b) * (Im a + - Im b))%Re).
                 { by rewrite /Rsqr. } rewrite -H7. apply Rsqr_pos_lt.
                 by apply Rminus_eq_contra.
               * repeat apply Rplus_le_le_0_compat.
                  - assert ((Re a ^+ 2)%Re = Rsqr (Re a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Re c ^+ 2)%Re = Rsqr (Re c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im a ^+ 2)%Re = Rsqr (Im a)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert ((Im c ^+ 2)%Re = Rsqr (Im c)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re a + - Re b)%Re ^+ 2)%Re = Rsqr ((Re a + - Re b)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Re b + - Re c)%Re ^+ 2)%Re = Rsqr ((Re b + - Re c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
                  - assert (((Im b + - Im c)%Re ^+ 2)%Re = Rsqr ((Im b + - Im c)%Re)).
                    { unfold Rsqr. by rewrite expr2 RmultE. }
                    rewrite H7. apply Rle_0_sqr .
  - rewrite !expr2 -!RmultE. nra.
  - rewrite !expr2 -!RmultE. nra.
  - rewrite !expr2 -!RmultE. nra.
Qed.


Lemma Ah_is_symmetric (h:R):
  forall (i j:'I_3), (Ah 2%N h) i j = (Ah 2%N h) j i.
Proof.
intros. rewrite /Ah !mxE.
assert ((i<=j)%coq_nat \/ (i > j)%coq_nat). { lia. }
destruct H.
+ assert ((i <= j)%N). { by apply /ssrnat.leP. }
  rewrite leq_eqVlt in H0.
  assert ((i == j :>nat) \/ (i < j)%N). { by apply /orP. }
  destruct H1.
  - rewrite H1. by rewrite eq_sym H1.
  - assert (i == j :> nat = false). { by apply ltn_eqF. } rewrite H2.
    assert (j == i :> nat = false). { rewrite eq_sym. by apply ltn_eqF. }
    rewrite H3.
    assert ((i - j)%N == 1%N = false).
    { assert ((i-j)%N = 0%N).
      { apply /eqP. apply ltnW in H1. rewrite -subn_eq0 in H1.
        by rewrite H1.
      } by rewrite H4.
    } by rewrite H4.
+ assert ((j < i)%N). { by apply /ssrnat.leP. }
  assert (j == i :>nat = false). { by apply ltn_eqF. } rewrite H1.
  assert (i == j :> nat = false). { rewrite eq_sym. by apply ltn_eqF. } rewrite H2.
  assert ((j - i)%N == 1%N = false).
  { assert ((j-i)%N = 0%N).
    { apply /eqP. apply ltnW in H0. rewrite -subn_eq0 in H0.
      by rewrite H0.
    } by rewrite H3.
  } by rewrite H3.
Qed.



Lemma Ah_is_invertible:
  forall (h:R), (0 < h)%Re -> (Ah 2%N h) \in unitmx.
Proof.
intros. rewrite unitmxE.
assert (\det (Ah 2%N h) = (4/ h^6)%Re).
{ rewrite (expand_det_row _ 0). rewrite /cofactor //=.
  rewrite !big_ord_recr //= big_ord0 add0r addn0 addn1 addn2.
  assert ((widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max)) = 0).
  {  by apply /eqP. } rewrite !H0.
  assert ((widen_ord (leqnSn 2) ord_max) = 1).
  {  by apply /eqP. } rewrite !H1.
  assert (@ord_max 2 = 2). { by apply /eqP. } rewrite H2.
  assert ( Ah 2 h 0 2  = 0).
  { rewrite !mxE. simpl. by rewrite Rmult_0_r. } rewrite H3. rewrite mul0r.
  rewrite addr0. rewrite expr0 expr1 mul1r.
  assert (\det (row' 0 (col' 0 (Ah 2 h))) = (3 / h^4)%Re).
  { rewrite (expand_det_row _ 0) //=.
    rewrite !big_ord_recr //= big_ord0 add0r !mxE //=.
    assert (cofactor (row' 0 (col' 0 (Ah 2 h))) 0
              (widen_ord (leqnSn 1) ord_max)  = (2 / (h^2))%Re).
    { rewrite /cofactor //= addn0 expr0 mul1r.
      rewrite det_mx11 !mxE //=.
      assert ((2 / (h * (h * 1)))%Re = (2 * (/ (h * (h * 1))))%Re).
      { nra. } rewrite H4. rewrite Rmult_comm.
      assert ((1 / (h * (h * 1)))%Re = (/ (h * (h * 1)))%Re).
      { nra. } by rewrite H5.
    } rewrite H4.
    assert ( cofactor (row' 0 (col' 0 (Ah 2 h))) 0 ord_max = (1 / (h^2))%Re).
    { rewrite /cofactor //= addn1 expr1.
      rewrite det_mx11 !mxE //=. rewrite -RmultE.
      assert ((-1 * (1 / (h * (h * 1)) * -1))%Re = ((-1 * -1) * (1 / (h * (h * 1))))%Re).
      { nra. } rewrite H5.
      assert ((-1 * -1)%Re = 1%Re). { nra. } rewrite H6. nra.
    } rewrite H5.
    assert ((1 / (h * (h * 1)) * 2)%Re * (2 / h ^ 2)%Re = ( 4 / (h^4))%Re).
    { assert ((1 / (h * (h * 1)) * 2)%Re = (2 / h ^ 2)%Re).
      { assert ((1 / (h * (h * 1)) * 2)%Re = (2 * / (h * h))%Re).
        { rewrite Rmult_comm.
          assert ((1 / (h * (h * 1)))%Re = (/ (h * h))%Re).
          { rewrite Rmult_1_r. nra. } by rewrite H6.
        } rewrite H6.
        assert ((/ (h * h))%Re = (/ h ^ 2)%Re).
        { simpl. by rewrite Rmult_1_r. } rewrite H7. nra.
      } rewrite H6.
      assert ((2 / h ^ 2)%Re = (2 * (/ h^2))%Re). { nra. } rewrite !H7.
      assert ((2 * / h ^ 2)%Re * (2  * / h ^ 2)%Re = 4%Re * ( (/(h^2)) * (/(h^2)))%Re).
      { rewrite -!RmultE. nra. } rewrite H8.
      rewrite -Rinv_mult. rewrite -!RmultE.
      assert ((h ^ 2 * h ^ 2)%Re = (h ^ 4)%Re). { nra. } rewrite H9. nra.
    } rewrite H6.
    assert ((1 / (h * (h * 1)) * -1)%Re * (1 / h ^ 2)%Re = (- (1 / h^4))%Re).
    { rewrite -!RmultE. rewrite Rmult_1_r.
      assert ((1 / (h * h) * -1 * (1 / h ^ 2))%Re =
               ((-1) * (/ h ^ 2 * / h ^ 2))%Re).
      { assert ((1 / (h * h))%Re = (/ h ^ 2)%Re).
        { assert ((h*h)%Re = (h^2)%Re). { nra. } rewrite H7. nra. }
        rewrite H7. nra.
      } rewrite H7.
      assert (((/ h ^ 2 * / h ^ 2))%Re = ( / (h^2 * h^2))%Re).
      {  rewrite -Rinv_mult.
         + by [].
      } rewrite H8.
      assert ((h ^ 2 * h ^ 2)%Re = (h ^ 4)%Re). { nra. } rewrite H9.
      nra.
    } rewrite H7.
    assert ((h * (h * (h * (h * 1))))%Re = (h^4)%Re). { nra. } rewrite H8.
    rewrite -RplusE. nra.
   } rewrite H4.
   assert (\det (row' 0 (col' 1 (Ah 2 h))) = (- (2 / (h^4)))%Re).
   { rewrite (expand_det_row _ 0) //=.
     rewrite !big_ord_recr //= big_ord0 add0r !mxE //=.
     assert (cofactor (row' 0 (col' 1 (Ah 2 h))) 0
                (widen_ord (leqnSn 1) ord_max) = ( (2 / h^2))%Re).
     { rewrite /cofactor //= addn0 expr0 mul1r.
       rewrite det_mx11 !mxE //=. rewrite Rmult_comm.
       assert ((1 / (h * (h * 1)))%Re = ( / (h * (h * 1)))%Re).
       { nra. } by rewrite H5.
     } rewrite H5.
     assert (cofactor (row' 0 (col' 1 (Ah 2 h))) 0 ord_max = 0%Re).
     { rewrite /cofactor //= addn1 expr1.
       rewrite det_mx11 !mxE //=. rewrite Rmult_0_r. by rewrite mulr0.
     } rewrite H6. rewrite mulr0 addr0.
     rewrite -RmultE.
     assert (((h * (h * (h * (h * 1)))))%Re = (h^4)%Re).
     { nra. } rewrite H7.
     assert ((h * (h * 1))%Re = (h^2)%Re). { nra. } rewrite H8.
     assert ((1 / h ^ 2)%Re = (/h^2)%Re). { nra. } rewrite H9.
     assert (((2 / h ^ 2))%Re = (2 * /h^2)%Re). { nra. } rewrite H10.
     assert ((/ h ^ 2 * -1 * (2 * / h ^ 2))%Re = ((-2) * (/ h^2 * / h^2))%Re).
     { nra. } rewrite H11.
     assert ((/ h ^ 2 * / h ^ 2)%Re = (/ (h^2 * h^2))%Re).
     { rewrite -Rinv_mult.
       + by [].
     } rewrite H12.
     assert (((h ^ 2 * h ^ 2))%Re = (h ^ 4)%Re). { nra. } rewrite H13.
     nra.
   } rewrite H5. rewrite /Ah !mxE //=.
   assert ((1 / (h * (h * 1)) * 2)%Re = (2 / (h ^2))%Re).
   { assert ((h * (h * 1))%Re = (h^2)%Re). { nra. } rewrite H6.
     nra.
   } rewrite H6.
   assert ((h * (h * (h * (h * 1))))%Re = (h^4)%Re). { nra. } rewrite H7.
   assert ((1 / (h * (h * 1)) * -1)%Re = ((-1) / (h^2))%Re).
   { assert ((h * (h * 1))%Re = (h^2)%Re). { nra. } rewrite H8.
     nra.
   } rewrite H8.
   assert ((h * (h * h ^ 4))%Re = (h^6)%Re). { nra. } rewrite H9.
   assert ((2 / h ^ 2)%Re * (3 / h ^ 4)%Re = (6 / (h^6))%Re).
   { rewrite -RmultE.
     assert ((2 / h ^ 2 * (3 / h ^ 4))%Re  = (6 * (/ h^2 * / h^4))%Re).
     { nra. } rewrite H10.
     assert ((/ h ^ 2 * / h ^ 4)%Re = (/ h^6)%Re).
     { rewrite -Rinv_mult.
       - assert ((h ^ 2 * h ^ 4)%Re = (h ^ 6)%Re). { nra. } by rewrite H11.
     } rewrite H11. nra.
   } rewrite H10.
   assert ((-1 / h ^ 2)%Re * (-1 * (- (2 / h ^ 4))%Re) = (-2 / (h^6))%Re).
   { rewrite -!RmultE.
     assert ((-1 / h ^ 2 * (-1 * - (2 / h ^ 4)))%Re = ((-2) * (/h^2 * /h^4))%Re).
     { nra. } rewrite H11.
     rewrite -Rinv_mult.
     + assert ((h ^ 2 * h ^ 4)%Re = (h ^ 6)%Re). { nra. } rewrite H12.
       nra.
   } rewrite H11. rewrite -RplusE. nra.
}
rewrite H0. apply /unitrP.
exists ((h^6 / 4)%Re).
split.
+ assert ( (4 / h ^ 6)%Re = ( / (h^6 / 4))%Re).
  { rewrite Rinv_mult.
    + rewrite Rinv_inv.
      - by rewrite Rmult_comm.
  } rewrite H1. apply Rinv_r.
  apply Rmult_integral_contrapositive. split.
  - repeat apply Rmult_integral_contrapositive.
        split.
        * nra.
        * apply Rmult_integral_contrapositive. split.
          ++ nra.
          ++ apply Rmult_integral_contrapositive. split.
             -- nra.
             -- apply Rmult_integral_contrapositive. split.
                + nra.
                + apply Rmult_integral_contrapositive. split; nra.
  - nra.
+ assert ( (4 / h ^ 6)%Re = ( / (h^6 / 4))%Re).
  { rewrite Rinv_mult.
    + rewrite Rinv_inv.
      - by rewrite Rmult_comm.
  } rewrite H1. apply Rinv_l.
  apply Rmult_integral_contrapositive. split.
  - repeat apply Rmult_integral_contrapositive.
        split.
        * nra.
        * apply Rmult_integral_contrapositive. split.
          ++ nra.
          ++ apply Rmult_integral_contrapositive. split.
             -- nra.
             -- apply Rmult_integral_contrapositive. split.
                + nra.
                + apply Rmult_integral_contrapositive. split; nra.
  - nra.
Qed.

Theorem Gauss_seidel_Ah_converges:
  forall (b: 'cV[R]_3) (h:R),
  (0 < h)%Re ->
  let A := (Ah 2%N h) in
  let x:= (invmx A) *m b in
    forall x0: 'cV[R]_3,
        is_lim_seq (fun m:nat => vec_norm (addmx (X_m m.+1 x0 b (A1 A) (A2 A)) (oppmx x))) 0%Re.
Proof.
intros.
apply Gauss_Seidel_converges.
+ by apply Ah_is_invertible.
+ intros. rewrite /A0. rewrite !mxE.
  assert (i == i :>nat). { by []. }
  rewrite H0. apply /RltP.
  apply Rmult_lt_0_compat.
  - assert ((1 / h ^ 2)%Re = (/ (h^2))%Re). { nra. }
    rewrite H1. apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; nra.
  - apply Rlt_0_2.
+ intros. rewrite /A0.
  by apply Ah_is_symmetric.
+ by apply Ah_pd.
Qed.


