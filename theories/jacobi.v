(** Proof of the convergence of the Jacobi iterative process
  using an example **)
Require Import Reals Psatz R_sqrt R_sqr.
From mathcomp Require Import all_algebra all_ssreflect ssrnum bigop ssrnat.
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
Require Import complex_mat_vec_prop.
Require Import iter_necessity iter_convergence.

Import ComplexField.

(** define a tridiagonal system **)


Definition A (n:nat):= \matrix_(i<n.+1, j<n.+1)
   if (i==j :> nat) then (-2)%Re else
      (if ((i-j)%N==1%N :>nat) then (1)%Re else
            (if ((j-i)%N==1%N :>nat) then (1)%Re else 0)).


Definition Ah (n:nat)(h:R) := \matrix_(i<n.+1,j<n.+1)
    ((1/(h^2)) * ((A n) i j))%Re.


Definition d (n:nat) (A: 'M[R]_n):= \row_(i<n) A i i.

Definition diag_A (n:nat) (A: 'M[R]_n):=diag_mx (d A).

(** Define the A1 matrix for the Jacobi process **)
Definition A1_J (n:nat) (h:R):= diag_A (Ah n h).

(** stating the explicit inverse of A1 since it's diagonal **)
Lemma invmx_A1_J: forall (n:nat) (h:R),
  (0<h)%Re -> invmx (A1_J n h) = ((-(h^+2)/2) *: 1%:M)%Re.
Proof.
intros.
assert ((-(h^+2)/2) = (- (2 / (h^+2)))^-1).
{ rewrite -[RHS]div1r.
  rewrite -RoppE -!RpowE -!RdivE.
  + assert ((1 / (- (2 / h ^ 2)%Re)%Ri)%Re =
              (/ (- (2 / h ^ 2)%Re)%Ri)%Re). { nra. }
    rewrite H0. rewrite -Ropp_inv_permute.
    - assert ((- h ^ 2 / 2)%Re = (- ( h ^ 2 / 2))%Re).
      { nra. } rewrite H1. apply Ropp_eq_compat.
      rewrite Rinv_mult_distr.
      rewrite Rinv_involutive.
      * nra.
      * assert ( (0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re).
        { nra. } apply H2. apply Rmult_lt_0_compat; nra.
      *  nra.
    - assert ((0< / h ^ 2)%Re -> / h ^ 2 <> 0%Re). { nra. }
      apply H2. apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; nra.
  + assert ((0 < (2 / h ^ 2))%Re -> (2 / h ^ 2)%Re <> 0%Re).
    { nra. } apply H1. apply Rmult_lt_0_compat.
    - nra.
    - apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; nra.
  + apply /eqP.
    assert ( (0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re).
    { nra. } apply H0. apply Rmult_lt_0_compat; nra.
  + apply /eqP. apply Ropp_neq_0_compat.
    assert ((0 < (2 / h ^ 2) )%Re -> (2 / h ^ 2)%Re <> 0%Re).
    { nra. } apply H0. apply Rmult_lt_0_compat.
    - nra.
    - apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; nra.
  + apply /eqP.
    assert ( (0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re).
    { nra. } apply H0. apply Rmult_lt_0_compat; nra.
  + apply /eqP.
    assert ((0<2)%Re ->2%Re <> 0%Re). {  nra. } apply H0. nra.
} rewrite H0.
rewrite scalemx1 -invmx_scalar .
assert ((A1_J n h) = (- (2 / h ^+ 2))%:M).
{ apply matrixP. unfold eqrel. intros. rewrite !mxE.
  assert (x == x :> nat). { by []. } rewrite H1.
  assert ((1 / h ^ 2 * -2)%Re = (- (2 / h ^+ 2))%Re).
  { assert ((1 / h ^ 2 * -2)%Re = (- (2 / h^2))%Re).
    { nra. } rewrite H2. by rewrite RpowE.
  } rewrite H2. rewrite -RoppE -RdivE.
  + by [].
  + apply /eqP.
    assert ( (0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re).
    { nra. } rewrite -RpowE. apply H3. apply Rmult_lt_0_compat; nra.
} by rewrite H1.
Qed.

(** A1 * A1^-1 = I **)
Lemma invmx_A1_mul_A1_1:forall (n:nat) (h:R),
  (0<h)%Re -> A1_J n h *m invmx (A1_J n h) = 1%:M.
Proof.
intros. apply mulmx1C. rewrite invmx_A1_J.
+ rewrite scalemx1 mul_scalar_mx.
  apply matrixP. unfold eqrel. intros.
  rewrite !mxE //=.
  assert (x == x :> nat). { by []. } rewrite H0.
  rewrite !Rmult_1_r. rewrite mulrnAr.
  assert (((- h ^+ 2)%Ri * 2^-1 * (1 / (h * h) * -2))%Re = 1%Re).
  { rewrite -RoppE.
    assert ((- h ^+ 2 * 2^-1 * (1 / (h * h) * -2))%Re  =
            ( h ^+ 2 * 2^-1 * (1 / (h * h) * 2))%Re ).
    { nra. } rewrite H1. clear H1.
    assert (((h ^+2) * 2^-1 * (1 / (h * h)))%Re = (1 / 2)%Re ).
    { assert ((1 / (h * h))%Re = (/ (h^2))%Re).
      { assert ((h * h)%Re = (h^2)%Re). { nra. } rewrite H1. nra.
      } rewrite H1. rewrite -div1r. rewrite -RdivE.
      + assert (((h ^+2) * (1 / 2) * / h ^ 2)%Re =
                  ((1 / 2) * ((h ^+2) *  / h ^ 2))%Re).
        { nra. } rewrite H2. rewrite !RmultE.
        assert ((h ^+2 * / h ^ 2) = 1%Re).
        { assert ((h ^2 * / h ^ 2)%Re = 1%Re).
          { apply Rinv_r.
            assert ((0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re). { nra. }
            apply H3. apply Rmult_lt_0_compat;nra.
          } rewrite -H3. rewrite [RHS]RmultE.
          apply  Rmult_eq_compat_r. by rewrite RpowE.
        } rewrite H3. by rewrite mulr1.
      + apply /eqP. assert ( (0<2)%Re -> 2%Re <> 0%Re). { nra. }
        apply H2. nra.
    }
    assert ((h ^+ 2 * 2^-1 * (1 / (h * h) * 2))%Re =
              ((h ^+ 2 * 2^-1 * (1 / (h * h))) * 2)%Re).
    { nra. } rewrite H2. rewrite H1. nra.
  } rewrite -!RmultE. rewrite H1. by [].
+ by [].
Qed.

(** A1 is invertible **)
Lemma A1_invertible: forall (n:nat) (h:R),
  (0<h)%Re -> A1_J n h \in unitmx.
Proof.
intros. rewrite unitmxE. rewrite unitrE. rewrite -det_inv.
rewrite -det_mulmx. rewrite invmx_A1_mul_A1_1. by rewrite det1.
by [].
Qed.

(** Define the A2 matrix of the Jacobi process **)
Definition A2_J (n:nat) (h:R):=
  addmx (Ah n h) (oppmx (A1_J n h)).

(** Define the iteration matrix for the Jacobi method **)
Definition S_mat_J (n:nat) (h:R):=
   RtoC_mat (oppmx (mulmx ((invmx (A1_J n h))) (A2_J n h))).

(** S_mat = (I - D^-1 A). Hence S_mat is tridiagonal **)
Lemma S_mat_simp:
  forall (n:nat) (h:R),
  (0<h)%Re -> S_mat_J n h =
      RtoC_mat (addmx 1%:M (oppmx (mulmx (invmx (A1_J n h)) (Ah n h)))).
Proof.
intros. rewrite /S_mat_J. apply matrixP. unfold eqrel.
intros. rewrite mxE.  rewrite [RHS]mxE. apply /eqP.
rewrite eq_complex //=. apply /andP. split.
+ apply /eqP. rewrite mxE. rewrite [RHS]mxE. rewrite /A2_J.
  rewrite mulmxDr. rewrite -Mopp_mult_r.
  assert ((invmx (A1_J n h) *m A1_J n h) = 1%:M).
  { by apply inverse_A, A1_invertible. } rewrite H0.
  rewrite mxE. rewrite opprD. rewrite addrC.
  assert ( - @oppmx [ringType of R] n.+1 n.+1 1%:M x y = 1%:M x y) .
  { rewrite !mxE. rewrite -!mulNrn. by rewrite opprK. }
  rewrite H1.
  assert (- (invmx (A1_J n h) *m Ah n h) x y =
          oppmx (invmx (A1_J n h) *m Ah n h) x y).
  { by rewrite !mxE.  } by rewrite H2.
+ by [].
Qed.

Definition a (m:nat) (h:R) := (S_mat_J m h) (@inord m 1) 0.

Definition b (m:nat) (h:R) := (S_mat_J m h) 0 0.

Definition c (m:nat) (h:R) := (S_mat_J m h) 0 (@inord m 1).
Definition p (m:nat) (h:R) := ((a m h) * (c m h))%C.

(** Define the eigenvalue of the Jacobi iterative matrix **)
Definition lambda_J (m N:nat) (h:R) :=
  (b N h) + 2* sqrtc(p N h)* RtoC (cos((m.+1%:R * PI)*/ N.+2%:R)).

Definition Eigen_vec (m n:nat) (a b c:R):= \col_(i < n.+1)
   (sqrt ( 2 / INR (n+2))*(Rpower (a */c) (INR i +1 -1*/2))* sin(((INR i +1)*INR(m+1)*PI)*/INR (n+2))).



Definition a_A (m:nat) (h:R) := (Ah m h) (@inord m 1) 0.

Definition b_A (m:nat) (h:R) := (Ah m h) 0  0.

Definition c_A (m:nat) (h:R) := (Ah m h) 0 (@inord m 1).
Definition p_A (m:nat) (h:R) := ((a_A m h) * (c_A m h))%Re.

(** Define the eigenvalue of the Ah matrix **)
Definition Lambda_Ah (m N:nat) (h:R) :=
   (b_A N h) + 2* sqrt(p_A N h)* (cos((m.+1%:R * PI)*/ N.+2%:R)).


Lemma Im_p_0: forall (n:nat) (h:R), (0<h)%Re -> Im (p n h) = 0.
Proof.
intros. rewrite /p /a /c Im_complex_prod.
assert ( Im (S_mat_J n h 0 (inord 1)) = 0%Re).
{ rewrite S_mat_simp.
  + by rewrite /RtoC_mat mxE /=.
  + by [].
} rewrite H0.
assert (Im (S_mat_J n h (inord 1) 0) = 0%Re).
{ rewrite S_mat_simp.
  + by rewrite /RtoC_mat mxE /=.
  + by [].
} rewrite H1.
by rewrite mulr0 mul0r addr0.
Qed.


Lemma D_inv_A:forall (n:nat) (h:R),
  (0<h)%Re -> (oppmx (mulmx (invmx (A1_J n h)) (Ah n h))) =
    oppmx ((-(h^+2)/2) *: (Ah n h)).
Proof.
intros. apply matrixP. unfold eqrel. intros. rewrite invmx_A1_J.
+ by rewrite scalemx1 mul_scalar_mx.
+ by [].
Qed.


Lemma Re_p_ge_0: forall (n:nat) (h:R),
  (0<n)%N -> (0<h)%Re -> (0 <= Re (p n h))%Re.
Proof.
intros. rewrite /p /a /c Re_complex_prod.
assert ( Im (S_mat_J n h 0 (inord 1)) = 0%Re).
{ rewrite S_mat_simp.
  + by rewrite /RtoC_mat mxE /=.
  + by [].
} rewrite H1.
assert (Im (S_mat_J n h (inord 1) 0) = 0%Re).
{ rewrite S_mat_simp.
  + by rewrite /RtoC_mat mxE /=.
  + by [].
}  rewrite H2.
rewrite mulr0 subr0 -RmultE.
rewrite !S_mat_simp.
+ rewrite !D_inv_A.
  rewrite  !/RtoC_mat !mxE //= eq_sym.
  assert ((0%N == @inord n 1 :> nat)%:R = 0%Re).
  { assert (@inord n 1 = 1%N :> nat). { by rewrite inordK. }
    by rewrite H3.
  } rewrite H3. rewrite !sub0r. rewrite eq_sym.
  assert (0%N == @inord n 1 :> nat = false).
  { assert (@inord n 1 = 1%N :> nat). { by rewrite inordK. }
    by rewrite H4.
  } rewrite H4.
  assert ((@inord n 1 - 0)%N == 1%N).
  { by rewrite inordK. } rewrite H5.
  rewrite -RoppE -!RmultE.
  assert (((h ^+2) * 2^-1 * (1 / (h * (h * 1)) * 1))%Re = (1 / 2)%Re ).
  { assert ((1 / (h * (h * 1)) * 1)%Re = (/ (h^2))%Re).
    { rewrite !Rmult_1_r.
      assert ((h * h)%Re = (h^2)%Re). { nra. } rewrite H6. nra.
    } rewrite H6. rewrite -div1r. rewrite -RdivE.
    + assert (((h ^+2) * (1 / 2) * / h ^ 2)%Re =
                ((1 / 2) * ((h ^+2) *  / h ^ 2))%Re).
      { nra. } rewrite H7. rewrite !RmultE.
      assert ((h ^+2 * / h ^ 2) = 1%Re).
      { assert ((h ^2 * / h ^ 2)%Re = 1%Re).
        { apply Rinv_r.
          assert ((0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re). { nra. }
          apply H8. apply Rmult_lt_0_compat;nra.
        } rewrite -H8. rewrite [RHS]RmultE.
        apply  Rmult_eq_compat_r. by rewrite RpowE.
      } rewrite H8. by rewrite mulr1.
    + apply /eqP. assert ( (0<2)%Re -> 2%Re <> 0%Re). { nra. }
      apply H7. nra.
  } rewrite -RoppE.
  assert ((- (- h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1)))%Re =
            (h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1))%Re).
  { nra. } rewrite H7.
  rewrite H6. nra.
+ by []. by [].
Qed.



Lemma p_destruct:forall (n:nat) (h:R),
  (0<n)%N -> (0<h)%Re -> sqrtc (p n h) = (sqrt (Re (p n h)) +i* 0)%C.
Proof.
intros. rewrite sqrtc_sqrtr.
+ apply /eqP. rewrite eq_complex //=.  rewrite RsqrtE.
  apply /andP. split; by [].
  apply /RleP. by apply Re_p_ge_0.
+ rewrite lecE //=. apply /andP. split.
  - apply /eqP. by apply Im_p_0.
  - apply /RleP. by apply Re_p_ge_0.
Qed.


Lemma sqrt_p_evals: forall (n:nat) (h:R),
  (0<h)%Re -> (0< n)%N -> sqrt (Re (a n h * c n h)) = (1/2)%Re.
Proof.
intros.
rewrite /a /c Re_complex_prod.
assert ( Im (S_mat_J n h 0 (inord 1)) = 0%Re).
{ rewrite S_mat_simp.
  + by rewrite /RtoC_mat mxE /=.
  + by [].
} rewrite H1.
assert (Im (S_mat_J n h (inord 1) 0) = 0%Re).
{ rewrite S_mat_simp.
  + by rewrite /RtoC_mat mxE /=.
  + by [].
}  rewrite H2.
rewrite mulr0 subr0. rewrite -RmultE.
rewrite !S_mat_simp.
+ rewrite !D_inv_A.
  rewrite  !/RtoC_mat !mxE //= eq_sym.
  assert (0%N == @inord n 1 :> nat = false).
  { assert (@inord n 1 = 1%N :> nat). { by rewrite inordK. }
    by rewrite H3.
  } rewrite !H3.
  assert ((0%N  == @inord n 1 :> nat)%:R = 0%Re).
  { by rewrite H3. } rewrite !H4 !sub0r.
  assert (@inord n 1 == 0%N :> nat = false).
  { by rewrite eq_sym H3. } rewrite H5.
  assert (@inord n 1 = 1%N :> nat). { by rewrite inordK. }
  rewrite H6 //=.
  rewrite -RoppE -!RmultE.
  assert (((h ^+2) * 2^-1 * (1 / (h * (h * 1)) * 1))%Re = (1 / 2)%Re ).
  { assert ((1 / (h * (h * 1)) * 1)%Re = (/ (h^2))%Re).
    { rewrite !Rmult_1_r.
      assert ((h * h)%Re = (h^2)%Re). { nra. } rewrite H7. nra.
    } rewrite H7. rewrite -div1r. rewrite -RdivE.
    + assert (((h ^+2) * (1 / 2) * / h ^ 2)%Re =
                ((1 / 2) * ((h ^+2) *  / h ^ 2))%Re).
      { nra. } rewrite H8. rewrite !RmultE.
      assert ((h ^+2 * / h ^ 2) = 1%Re).
      { assert ((h ^2 * / h ^ 2)%Re = 1%Re).
        { apply Rinv_r.
          assert ((0< (h ^ 2))%Re -> (h ^ 2)%Re <> 0%Re). { nra. }
          apply H9. apply Rmult_lt_0_compat;nra.
        } rewrite -H9. rewrite [RHS]RmultE.
        apply  Rmult_eq_compat_r. by rewrite RpowE.
      } rewrite H9. by rewrite mulr1.
    + apply /eqP. assert ( (0<2)%Re -> 2%Re <> 0%Re). { nra. }
      apply H8. nra.
  } rewrite -RoppE.
  assert ((- (- h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1)))%Re =
            (h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1))%Re).
  { nra. } rewrite H8. rewrite H7.
  rewrite sqrt_square; nra. by [].
+ by [].
Qed.

(** Re (\lambda_J )= 1+ h^2/2 * (\lambda (Ah)) **)
Lemma lambda_simp: forall (m N:nat) (h:R),
  (0<h)%Re -> (0< N)%N ->
  Re (lambda_J m N h) = (1 + ((h^2)/2)  * (Lambda_Ah m N h))%Re.
Proof.
intros. rewrite /lambda_J. rewrite Re_add Re_complex_prod /RtoC //=.
rewrite mulr0 subr0. rewrite Re_complex_prod //= addr0 mul0r subr0.
rewrite p_destruct //=. rewrite /p.
rewrite /b mxE //=. rewrite invmx_A1_J.
rewrite scalemx1 mul_scalar_mx. rewrite !mxE //=.
rewrite mulr1n.
assert ((- h ^+ 2 / 2 *
           ((1 / (h * (h * 1)) * -2)%Re -
            (1 / (h * (h * 1)) * -2)%Re)) = 0%Re).
{ rewrite -RplusE -RoppE.
  assert ((1 / (h * (h * 1)) * -2 +
              - (1 / (h * (h * 1)) * -2))%Re = 0%Re).
  { nra. } rewrite H1. by rewrite mulr0.
} rewrite H1. clear H1. rewrite oppr0 add0r. rewrite -!RmultE.
rewrite -RplusE.
assert ((1 + 1)%Re = 2%Re). { nra. } rewrite H1.
rewrite /Lambda_Ah.
assert ( b_A N h = ((-2) / (h^2))%Re).
{ rewrite /b_A /Ah mxE /A mxE /=. nra. }
  rewrite H2.
  assert ( sqrt (p_A N h) = ( 1 / (h^2))%Re).
  { rewrite /p_A.
    assert ( a_A N h = (1 / h ^ 2)%Re).
    { rewrite /a_A /Ah mxE /A mxE //=.
      assert ((@inord N 1) = 1%N :> nat).
      { by rewrite inordK. } rewrite !H3 //=.
      rewrite !Rmult_1_r. nra.
    } rewrite H3.
    assert ( c_A N h = (1 / h ^ 2)%Re).
    { rewrite /c_A /Ah mxE /A mxE //=.
      assert ((@inord N 1) = 1%N :> nat).
      { by rewrite inordK. } rewrite !H4 //=.
      rewrite !Rmult_1_r. nra.
    } rewrite H4. rewrite sqrt_square.
    * by [].
    * apply Rlt_le.
      assert ((1 / h ^ 2)%Re = (/ (h^2))%Re). { nra. } rewrite H5.
      apply Rinv_0_lt_compat, Rmult_lt_0_compat; nra.
  } rewrite H3.
assert ((2 * (1 / h ^ 2)%Re) = (2 / (h^2))%Re).
{ apply Rmult_eq_compat_l. nra.  } rewrite H4.
assert ((-2 / h ^ 2)%Re = ((2 / h ^ 2)%Re * (-1))%Re).
{ nra. } rewrite H5.
rewrite -RplusE -RmultE.
assert ((2 / h ^ 2 * -1 +
            2 / h ^ 2 * cos ((succn m)%:R * PI * / (succn N.+1)%:R))%Re =
            ((2 / (h^2)) * (-1 + (cos ((succn m)%:R * PI * / (succn N.+1)%:R))))%Re).
{ nra. } rewrite H6.
assert ( (h * (h * 1) / 2 *
           (2 / h ^ 2 *
            (-1 + cos ((succn m)%:R * PI * / (succn N.+1)%:R))))%Re  =
         (((h * (h * 1) / 2) * (2 / h ^ 2))%Re *
          (-1 + cos ((succn m)%:R * PI * / (succn N.+1)%:R)))%Re).
{ nra. } rewrite H7. clear H7.
assert (((h * (h * 1) / 2) * (2 / h ^ 2))%Re  = 1%Re).
{ rewrite Rmult_1_r.
  assert ((2 / h ^ 2)%Re = (/ (h * h / 2))%Re).
  { rewrite Rinv_mult_distr.
    + rewrite Rinv_involutive.
      - assert ((h * h)%Re = (h^2)%Re). { nra. } rewrite H7.
        nra.
      - nra.
    + assert ( (0 < (h * h))%Re -> (h * h)%Re <> 0%Re). { nra. }
      apply H7. apply Rmult_lt_0_compat; nra.
    + assert ( (0< /2)%Re -> / 2 <> 0%Re). { nra. }
      apply H7. apply Rinv_0_lt_compat; nra.
  } rewrite H7. apply Rinv_r.
  assert ((0< (h * h / 2))%Re -> (h * h / 2)%Re <> 0%Re).
  { nra. } apply H8. apply Rmult_lt_0_compat.
  + apply Rmult_lt_0_compat; nra.
  + apply Rinv_0_lt_compat; nra.
} rewrite H7. rewrite Rmult_1_l.
assert ((1 + (-1 + cos ((succn m)%:R * PI * / (succn N.+1)%:R)))%Re =
          cos ((succn m)%:R * PI * / (succn N.+1)%:R)).
{ nra. } rewrite H8.
assert (cos ((succn m)%:R * PI * / (succn N.+1)%:R) =
          (1* (cos ((succn m)%:R * PI * / (succn N.+1)%:R)))%Re).
{ nra. } rewrite [RHS]H9.
apply Rmult_eq_compat_r. rewrite RmultE.
rewrite sqrt_p_evals.
+ assert ((1 / 2)%Re = (/2)%Re). { nra. } rewrite H10.
  rewrite -RmultE. rewrite Rinv_r; nra.
+ by [].
+ by []. apply H.
Qed.

(** Re (\lambda_J) < 1 **)
Lemma Jacobi_converges_aux:
  forall (m n:nat) (h:R), (0< h)%Re ->(0<n)%N ->
  (m < n.+1)%N ->
  ((1 + ((h^2)/2)  * (Lambda_Ah m n h)) < 1)%Re.
Proof.
intros.
assert ( 1%Re = (1 + 0)%Re). { nra. } rewrite H2.
assert ((1 + 0 + h ^ 2 / 2 * Lambda_Ah m n h)%Re =
          (1 + ((h^2)/2)  * (Lambda_Ah m n h))%Re). { nra. }
rewrite H3. clear H2 H3.
apply Rplus_le_lt_compat.
+ nra.
+ assert ( 0%Re = ((h ^ 2 / 2)*0)%Re). { nra. } rewrite H2.
  clear H2. apply Rmult_lt_compat_l.
  - apply Rmult_lt_0_compat.
    * apply Rmult_lt_0_compat; nra.
    * apply Rinv_0_lt_compat; nra.
  - rewrite /Lambda_Ah.
    assert ( b_A n h = ((-2) / (h^2))%Re).
    { rewrite /b_A /Ah mxE /A mxE//=. nra. }
    rewrite H2.
    assert ( sqrt (p_A n h) = ( 1 / (h^2))%Re).
    { rewrite /p_A.
      assert ( a_A n h = (1 / h ^ 2)%Re).
      { rewrite /a_A /Ah mxE /A mxE //=.
        assert ((@inord n 1) = 1%N :> nat).
        { by rewrite inordK. } rewrite !H3 //=.
        rewrite !Rmult_1_r. nra.
      } rewrite H3.
      assert ( c_A n h = (1 / h ^ 2)%Re).
      { rewrite /c_A /Ah mxE /A mxE //=.
        assert ((@inord n 1) = 1%N :> nat).
        { by rewrite inordK. } rewrite !H4 //=.
        rewrite !Rmult_1_r. nra.
      } rewrite H4. rewrite sqrt_square.
      * by [].
      * apply Rlt_le.
        assert ((1 / h ^ 2)%Re = (/ (h^2))%Re). { nra. } rewrite H5.
        apply Rinv_0_lt_compat, Rmult_lt_0_compat; nra.
    } rewrite H3.
    assert ((2 * (1 / h ^ 2)%Re) = (2 / (h^2))%Re).
    { apply Rmult_eq_compat_l. nra.  } rewrite H4.
    assert ((-2 / h ^ 2)%Re = ((2 / h ^ 2)%Re * (-1))%Re).
    { nra. } rewrite H5.
    rewrite -RplusE -RmultE.
    assert ((2 / h ^ 2 * -1 +
              2 / h ^ 2 * cos ((succn m)%:R * PI * / (succn n.+1)%:R))%Re =
              ((2 / (h^2)) * (-1 + (cos ((succn m)%:R * PI * / (succn n.+1)%:R))))%Re).
    { nra. } rewrite H6.
    assert ( 0%Re = ((2 / h ^ 2) * 0)%Re). { nra. } rewrite H7.
    apply Rmult_lt_compat_l.
    * apply Rmult_lt_0_compat.
      ++ nra.
      ++ apply Rinv_0_lt_compat, Rmult_lt_0_compat; nra.
    * assert (0%Re = ((-1) + 1)%Re). { nra. } rewrite H8.
      apply Rplus_le_lt_compat.
      ++ nra.
      ++ assert (cos 0 = 1%Re). { by apply cos_0. } rewrite -H9.
         apply cos_decreasing_1.
         - nra.
         - apply Rlt_le. apply PI_RGT_0.
         - apply Rlt_le.
           assert (((succn m)%:R * PI * / (succn n.+1)%:R)%Re =
                    (((succn m)%:R * PI)  / (succn n.+1)%:R)%Re).
           { nra. } rewrite H10.
           apply Rmult_lt_0_compat.
           * apply Rmult_lt_0_compat.
             - by apply nat_ring_lt.
             - apply PI_RGT_0.
           * apply Rinv_0_lt_compat. by apply nat_ring_lt.
         - assert (PI = ((PI * ((succn n.+1)%:R) * / (succn n.+1)%:R))%Re).
           { rewrite Rmult_assoc. rewrite Rinv_r.
             + nra.
             + assert ((0< (succn n.+1)%:R )%Re -> (succn n.+1)%:R <> 0%Re).
               { nra. } apply H10. by apply nat_ring_lt.
           }
           assert ((((succn m)%:R * PI) * / (succn n.+1)%:R <=
                      ((PI * ((succn n.+1)%:R) * / (succn n.+1)%:R)))%Re ->
                      (((succn m)%:R * PI) * / (succn n.+1)%:R <= PI)%Re).
           { nra. } apply H11.
           apply Rmult_le_compat_r.
           * by apply Rlt_le, Rinv_0_lt_compat, nat_ring_lt.
           * rewrite Rmult_comm. apply Rmult_le_compat_l.
            ++ apply Rlt_le, PI_RGT_0.
            ++ by apply nat_ring_mn_le, ltnW.
         - apply Rmult_lt_0_compat.
           * apply Rmult_lt_0_compat.
             ++ by apply nat_ring_lt.
             ++ by apply PI_RGT_0.
           * by apply Rinv_0_lt_compat, nat_ring_lt.
Qed.

Lemma nat_ring_mn_lt: forall (m n:nat),
  (m< n)%N -> (m%:R < n%:R)%Re.
Proof.
intros. induction n.
+ by [].
+ rewrite leq_eqVlt in H.
  assert ( (m.+1 == n.+1) \/ (m.+1 < n.+1)%N).
  { by apply /orP. } destruct H0.
  - assert ( m.+1 = n.+1). { by apply /eqP. }
    rewrite -H1.
    assert ( m%:R = (m%:R + 0)%Re). { nra. } rewrite H2.
    rewrite -addn1 natrD -RplusE. apply Rplus_le_lt_compat.
    * nra.
    * apply Rlt_0_1.
  - assert ( m%:R = (m%:R + 0)%Re). { nra. } rewrite H1.
    rewrite -addn1 natrD -RplusE. apply Rplus_lt_compat.
    * by apply IHn.
    * apply Rlt_0_1.
Qed.


(** Re (\lambda_J) > -1 **)
Lemma lambda_J_gt_minus_1:
  forall (n:nat) (i: 'I_n.+1) (h:R),
  (0 < h)%Re -> (0 < n)%N ->
  ((- 1)%Re < Re (lambda_J i n h))%Re.
Proof.
intros. rewrite lambda_simp /Lambda_Ah.
+ assert ( b_A n h = ((-2) / (h^2))%Re).
  { rewrite /b_A /Ah mxE /A mxE//=. nra. }
  rewrite H1.
  assert ( sqrt (p_A n h) = ( 1 / (h^2))%Re).
  { rewrite /p_A.
    assert ( a_A n h = (1 / h ^ 2)%Re).
    { rewrite /a_A /Ah mxE /A mxE //=.
      assert ((@inord n 1) = 1%N :> nat).
      { by rewrite inordK. } rewrite !H2 //=.
        rewrite !Rmult_1_r. nra.
    } rewrite H2.
    assert ( c_A n h = (1 / h ^ 2)%Re).
    { rewrite /c_A /Ah mxE /A mxE //=.
      assert ((@inord n 1) = 1%N :> nat).
      { by rewrite inordK. } rewrite !H3 //=.
      rewrite !Rmult_1_r. nra.
    } rewrite H3. rewrite sqrt_square.
    + nra.
    + apply Rlt_le.
      assert ((1 / h ^ 2)%Re = (/ (h^2))%Re). { nra. } rewrite H4.
      apply Rinv_0_lt_compat, Rmult_lt_0_compat; nra.
  } rewrite H2.
  assert ((2 * (1 / h ^ 2)%Re) = (2 / (h^2))%Re).
  { apply Rmult_eq_compat_l. nra.  } rewrite H3.
  assert ((-2 / h ^ 2)%Re = ((2 / h ^ 2)%Re * (-1))%Re).
  { nra. } rewrite H4.
  rewrite -RplusE -RmultE.
  assert ((2 / h ^ 2 * -1 +
             2 / h ^ 2 * cos ((succn i)%:R * PI * / (succn n.+1)%:R))%Re =
             ((2 / (h^2)) * (-1 + (cos ((succn i)%:R * PI * / (succn n.+1)%:R))))%Re).
  { nra. } rewrite H5.
  assert ( (h ^ 2 / 2 *
               (2 / h ^ 2 *
                (-1 + cos ((succn i)%:R * PI * / (succn n.+1)%:R))))%Re =
            (((h ^ 2 / 2) * (2 / h ^ 2))%Re *
              (-1 + cos ((succn i)%:R * PI * / (succn n.+1)%:R)))%Re).
  { nra. } rewrite H6.
  assert ( ((h ^ 2 / 2) * (2 / h ^ 2))%Re = 1%Re).
  { assert ( (2 / h ^ 2)%Re = (/ (h ^ 2 / 2 ))%Re).
    { rewrite Rinv_mult_distr.
      + rewrite Rinv_involutive; nra.
      + assert ( (0 < (h ^ 2)%Re)%Re -> (h ^ 2)%Re <> 0%Re).
        { nra. } apply H7. apply Rmult_lt_0_compat; nra.
      + nra.
    } rewrite H7. rewrite Rinv_r. by [].
    assert ( (0 < (h ^ 2 / 2))%Re -> (h ^ 2 / 2)%Re <> 0%Re).
    { nra. } apply H8. apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; nra.
    + apply Rinv_0_lt_compat; nra.
  } rewrite H7. rewrite Rmult_1_l.
  assert ((1 + (-1 + cos ((succn i)%:R * PI * / (succn n.+1)%:R)))%Re =
            cos ((succn i)%:R * PI * / (succn n.+1)%:R)).
  { nra. } rewrite H8.
  assert (cos PI = (-1)%Re). { by apply cos_PI. } rewrite -H9.
  apply cos_decreasing_1.
  + apply Rlt_le. apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat.
      * by apply nat_ring_lt.
      * apply PI_RGT_0.
    - apply Rinv_0_lt_compat. by apply nat_ring_lt.
  + assert (PI = ((PI * ((succn n.+1)%:R) * / (succn n.+1)%:R))%Re).
    { rewrite Rmult_assoc. rewrite Rinv_r.
      + nra.
      + assert ((0< (succn n.+1)%:R )%Re -> (succn n.+1)%:R <> 0%Re).
        { nra. } apply H10. by apply nat_ring_lt.
    }
    assert ((((succn i)%:R * PI) * / (succn n.+1)%:R <=
             ((PI * ((succn n.+1)%:R) * / (succn n.+1)%:R)))%Re ->
                (((succn i)%:R * PI) * / (succn n.+1)%:R <= PI)%Re).
    { nra. } apply H11.
    apply Rmult_le_compat_r.
    - by apply Rlt_le, Rinv_0_lt_compat, nat_ring_lt.
    - rewrite Rmult_comm. apply Rmult_le_compat_l.
      * apply Rlt_le, PI_RGT_0.
      * apply nat_ring_mn_le. apply ltn_trans with n.+1.
        ++ by [].
        ++ by [].
  + apply Rlt_le, PI_RGT_0.
  + nra.
  + assert (PI = ((PI * ((succn n.+1)%:R) * / (succn n.+1)%:R))%Re).
    { rewrite Rmult_assoc. rewrite Rinv_r.
      + nra.
      + assert ((0< (succn n.+1)%:R )%Re -> (succn n.+1)%:R <> 0%Re).
        { nra. } apply H10. by apply nat_ring_lt.
    }
    assert ((((succn i)%:R * PI) * / (succn n.+1)%:R <
             ((PI * ((succn n.+1)%:R) * / (succn n.+1)%:R)))%Re ->
                (((succn i)%:R * PI) * / (succn n.+1)%:R < PI)%Re).
    { nra. } apply H11.
    apply Rmult_lt_compat_r.
    - by apply Rinv_0_lt_compat, nat_ring_lt.
    - rewrite Rmult_comm. apply Rmult_lt_compat_l.
      * apply PI_RGT_0.
      * apply nat_ring_mn_lt.
        assert (i.+1 = (i+1)%N). { by rewrite -addn1. }
        rewrite H12.
        assert ((n.+1).+1 = ((n.+1) + 1)%N). { by rewrite -addn1. }
        rewrite H13. by rewrite ltn_add2r.
+ by [].
+ by [].
Qed.


Lemma Im_b_0: forall (n:nat) (h:R),
  Im (b n h) = 0%Re.
Proof.
intros. rewrite /b //= mxE //=.
Qed.

Lemma Rmult_le_compat_0: forall (x y :R),
  (0 <= x)%Re -> (0<=y)%Re  -> (0 <= x*y)%Re.
Proof.
intros. assert (0%Re = (0 * 0)%Re). { nra. } rewrite H1.
apply Rmult_le_compat; nra.
Qed.


Lemma Im_p_sqrt_0:  forall (n:nat) (h:R),
  (0<n)%N -> (0<h)%Re -> Im (sqrtc (p n h)) = 0%Re.
Proof.
intros. by rewrite p_destruct //=.
Qed.


Lemma Im_lambda_J_eq_0:
  forall (n:nat) (i: 'I_n.+1) (h:R),
  (0 < h)%Re -> (0 < n)%N ->
  (Im (lambda_J i n h)) = 0%Re.
Proof.
intros. rewrite /lambda_J Im_add !Im_complex_prod /RtoC //=.
rewrite !add0r mul0r addr0 mulr0 add0r //=.
rewrite Im_b_0 Im_p_sqrt_0. rewrite add0r. by rewrite -mulrA mul0r mulr0.
by []. apply H.
Qed.

(** Theorem for convrgence of the Jacobi iterative method **)
Theorem eig_less_than_1:
  forall (n:nat) (i: 'I_n.+1) (h:R),
  (0 < h)%Re -> (0 < n)%N ->
  (C_mod (lambda_J i n h) < 1)%Re.
Proof.
intros. rewrite /C_mod.
assert ((Im (lambda_J i n h)) = 0%Re). { by apply Im_lambda_J_eq_0. }
rewrite H1 !expr2 mulr0 -RmultE.
assert ((Re (lambda_J i n h) * Re (lambda_J i n h) + 0)%Re =
        (Re (lambda_J i n h) * Re (lambda_J i n h) )%Re).
{ nra. } rewrite H2.
assert (Rsqr (Re (lambda_J i n h)) =
          (Re (lambda_J i n h) * Re (lambda_J i n h))%Re).
{ by rewrite /Rsqr. } rewrite -H3.
rewrite sqrt_Rsqr_abs. apply Rabs_def1.
+ rewrite lambda_simp.
  - by apply Jacobi_converges_aux.
  - by [].
  - by [].
+ by apply lambda_J_gt_minus_1.
Qed.

Lemma Ah_J_split: forall (n:nat) (h:R),
  Ah n h = A1_J n h + A2_J n h.
Proof.
intros.
apply matrixP. unfold eqrel. intros. rewrite !mxE.
assert (x == x:> nat). { by apply /eqP. } rewrite H //=.
rewrite addrC. rewrite -addrA.
assert (((1 / (h * (h * 1)) * -2)%Re *- (x == y) +
            (1 / (h * (h * 1)) * -2)%Re *+ (x == y)) = 0).
{ apply /eqP. by rewrite addr_eq0. } rewrite H0. by rewrite addr0.
Qed.


Hypothesis Lambda_eq: forall (n:nat) (h:R) (i: 'I_n.+1),
  let S_mat :=
  RtoC_mat
    (oppmx (invmx (A1_J n h) *m A2_J n h)) in
  lambda S_mat i = lambda_J i n h.

Lemma Ah_is_invertible:
  forall (h:R), (0 < h)%Re -> (Ah 2%N h) \in unitmx.
Proof.
intros. rewrite unitmxE.
assert (\det (Ah 2%N h) = (-4/ h^6)%Re).
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
              (widen_ord (leqnSn 1) ord_max)  = (-2 / (h^2))%Re).
    { rewrite /cofactor //= addn0 expr0 mul1r.
      rewrite det_mx11 !mxE //=.
      assert ((-2 / (h * (h * 1)))%Re = (-2 * (/ (h * (h * 1))))%Re).
      { nra. } rewrite H4. rewrite Rmult_comm.
      assert ((1 / (h * (h * 1)))%Re = (/ (h * (h * 1)))%Re).
      { nra. } by rewrite H5.
    } rewrite H4.
    assert ( cofactor (row' 0 (col' 0 (Ah 2 h))) 0 ord_max = (-1 / (h^2))%Re).
    { rewrite /cofactor //= addn1 expr1.
      rewrite det_mx11 !mxE //=. rewrite -RmultE.
      assert ((-1 * (1 / (h * (h * 1)) * 1))%Re = ((-1 * 1) * (1 / (h * (h * 1))))%Re).
      { nra. } rewrite H5.
      assert ((-1 * 1)%Re = (-1)%Re). { nra. } rewrite H6. nra.
    } rewrite H5.
    assert ((1 / (h * (h * 1)) * -2)%Re * (-2 / h ^ 2)%Re = ( 4 / (h^4))%Re).
    { assert ((1 / (h * (h * 1)) * -2)%Re = (-2 / h ^ 2)%Re).
      { assert ((1 / (h * (h * 1)) * -2)%Re = (-2 * / (h * h))%Re).
        { rewrite Rmult_comm.
          assert ((1 / (h * (h * 1)))%Re = (/ (h * h))%Re).
          { rewrite Rmult_1_r. nra. } by rewrite H6.
        } rewrite H6.
        assert ((/ (h * h))%Re = (/ h ^ 2)%Re).
        { simpl. by rewrite Rmult_1_r. } rewrite H7. nra.
      } rewrite H6.
      assert ((-2 / h ^ 2)%Re = (-2 * (/ h^2))%Re). { nra. } rewrite !H7.
      assert ((-2 * / h ^ 2)%Re * (-2  * / h ^ 2)%Re = 4%Re * ( (/(h^2)) * (/(h^2)))%Re).
      { rewrite -!RmultE. nra. } rewrite H8.
      rewrite -Rinv_mult_distr. rewrite -!RmultE.
      assert ((h ^ 2 * h ^ 2)%Re = (h ^ 4)%Re). { nra. } rewrite H9. nra.
      apply Rmult_integral_contrapositive.
      split; nra.
      apply Rmult_integral_contrapositive.
      split; nra.
    } rewrite H6.
    assert ((1 / (h * (h * 1)) * 1)%Re * (-1 / h ^ 2)%Re = (- (1 / h^4))%Re).
    { rewrite -!RmultE. rewrite !Rmult_1_r.
      assert ((1 / (h * h) * (-1 / h ^ 2))%Re =
               ((-1) * (/ h ^ 2 * / h ^ 2))%Re).
      { assert ((1 / (h * h))%Re = (/ h ^ 2)%Re).
        { assert ((h*h)%Re = (h^2)%Re). { nra. } rewrite H7. nra. }
        rewrite H7. nra.
      } rewrite H7.
      assert (((/ h ^ 2 * / h ^ 2))%Re = ( / (h^2 * h^2))%Re).
      {  rewrite -Rinv_mult_distr.
         + by [].
         + apply Rmult_integral_contrapositive.
           split; nra.
         + apply Rmult_integral_contrapositive.
           split; nra.
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
                (widen_ord (leqnSn 1) ord_max) = ( (-2 / h^2))%Re).
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
     assert (((-2 / h ^ 2))%Re = (-2 * /h^2)%Re). { nra. } rewrite H10.
     assert ((/ h ^ 2 * 1 * (-2 * / h ^ 2))%Re = ((-2) * (/ h^2 * / h^2))%Re).
     { nra. } rewrite H11.
     assert ((/ h ^ 2 * / h ^ 2)%Re = (/ (h^2 * h^2))%Re).
     { rewrite -Rinv_mult_distr.
       + by [].
       + apply Rmult_integral_contrapositive.
         split; nra.
       + apply Rmult_integral_contrapositive.
         split; nra.
     } rewrite H12.
     assert (((h ^ 2 * h ^ 2))%Re = (h ^ 4)%Re). { nra. } rewrite H13.
     nra.
   } rewrite H5. rewrite /Ah !mxE //=.
   assert ((1 / (h * (h * 1)) * -2)%Re = (-2 / (h ^2))%Re).
   { assert ((h * (h * 1))%Re = (h^2)%Re). { nra. } rewrite H6.
     nra.
   } rewrite H6.
   assert ((h * (h * (h * (h * 1))))%Re = (h^4)%Re). { nra. } rewrite H7.
   assert ((1 / (h * (h * 1)) * 1)%Re = ((1) / (h^2))%Re).
   { assert ((h * (h * 1))%Re = (h^2)%Re). { nra. } rewrite H8.
     nra.
   } rewrite H8.
   assert ((h * (h * h ^ 4))%Re = (h^6)%Re). { nra. } rewrite H9.
   assert ((-2 / h ^ 2)%Re * (3 / h ^ 4)%Re = (-6 / (h^6))%Re).
   { rewrite -RmultE.
     assert ((-2 / h ^ 2 * (3 / h ^ 4))%Re  = (-6 * (/ h^2 * / h^4))%Re).
     { nra. } rewrite H10.
     assert ((/ h ^ 2 * / h ^ 4)%Re = (/ h^6)%Re).
     { rewrite -Rinv_mult_distr.
       - assert ((h ^ 2 * h ^ 4)%Re = (h ^ 6)%Re). { nra. } by rewrite H11.
       - apply Rmult_integral_contrapositive.
         split; nra.
       - apply Rmult_integral_contrapositive.
         split.
         ++ nra.
         ++ apply Rmult_integral_contrapositive. nra.
     } rewrite H11. nra.
   } rewrite H10.
   assert ((1 / h ^ 2)%Re * (-1 * (- (2 / h ^ 4))%Re) = (2 / (h^6))%Re).
   { rewrite -!RmultE.
     assert ((1 / h ^ 2 * (-1 * - (2 / h ^ 4)))%Re = ((2) * (/h^2 * /h^4))%Re).
     { nra. } rewrite H11.
     rewrite -Rinv_mult_distr.
     + assert ((h ^ 2 * h ^ 4)%Re = (h ^ 6)%Re). { nra. } rewrite H12.
       nra.
     + apply Rmult_integral_contrapositive.
       split; nra.
     + apply Rmult_integral_contrapositive.
         split.
         ++ nra.
         ++ apply Rmult_integral_contrapositive. nra.
   } rewrite H11. rewrite -RplusE. nra.
}
rewrite H0. apply /unitrP.
exists ((h^6 / -4)%Re).
split.
+ assert ( (-4 / h ^ 6)%Re = ( / (h^6 / -4))%Re).
  { rewrite Rinv_mult_distr.
    + rewrite Rinv_involutive.
      - by rewrite Rmult_comm.
      - nra.
    + repeat apply Rmult_integral_contrapositive.
        split.
        * nra.
        * apply Rmult_integral_contrapositive. split.
          ++ nra.
          ++ apply Rmult_integral_contrapositive. split.
             -- nra.
             -- apply Rmult_integral_contrapositive. split.
                + nra.
                + apply Rmult_integral_contrapositive. split; nra.
    + nra.
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
+ assert ( (-4 / h ^ 6)%Re = ( / (h^6 / -4))%Re).
  { rewrite Rinv_mult_distr.
    + rewrite Rinv_involutive.
      - by rewrite Rmult_comm.
      - nra.
    + repeat apply Rmult_integral_contrapositive.
        split.
        * nra.
        * apply Rmult_integral_contrapositive. split.
          ++ nra.
          ++ apply Rmult_integral_contrapositive. split.
             -- nra.
             -- apply Rmult_integral_contrapositive. split.
                + nra.
                + apply Rmult_integral_contrapositive. split; nra.
    + nra.
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

Lemma rpower_1 : forall x:R, Rpower 1 x = 1.
Proof.
intros.
unfold Rpower.
assert (ln 1= 0). { apply ln_1. } rewrite H.
assert ((x * 0)%Re= 0%Re). { nra.  } rewrite H0.
assert (ln 1= 0%Re). { apply ln_1. } rewrite <- H1. apply exp_ln. apply Rlt_0_1.
Qed.


Lemma inr_to_R: forall (n:nat),
  INR n = n%:R.
Proof.
intros. induction n.
+ by [].
+ rewrite -addn1. rewrite plus_INR. rewrite natrD.
  rewrite IHn. by [].
Qed.

Lemma a_eq_c (h:R): (0 < h)%Re ->
  a 3 h = c 3 h.
Proof.
intros. rewrite /a /c. rewrite !mxE. rewrite !big_ord_recr //= !big_ord0.
rewrite invmx_A1_J.
+ assert ((widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max)) = 0).
  { by apply /eqP. } rewrite H0.
  assert ( (widen_ord (leqnSn 2) ord_max) = 1).
  { by apply /eqP. } rewrite H1.
  assert (widen_ord (leqnSn 3) 0 = 0). { by apply /eqP. } rewrite !H2.
  assert (widen_ord (leqnSn 3) 1 = 1). { by apply /eqP. } rewrite !H3.
  assert (widen_ord (leqnSn 3) ord_max = 2). { by apply /eqP. } rewrite !H4.
  rewrite !mxE //=.
  assert ((1 %% 4)%N = 1%N). { by []. } rewrite !H5 //=.
  rewrite inordK //=. rewrite !mulr0 !mulr1 add0r. rewrite !mul0r !addr0 //=.
  rewrite !mulr0n //=. rewrite !subr0.
  assert (@inord 3 1 = 1). {  apply (@inord_val 3 1). }
  rewrite H6 //=. rewrite mulr1n. rewrite !Rmult_0_r !Rmult_1_r. rewrite -RminusE.
  assert ((1 / (h * h) * -2 - 1 / (h * h) * -2)%Re = 0%Re). { nra. } rewrite H7.
  rewrite !mulr0 !mulr0n. rewrite !addr0 !subr0. by rewrite !add0r mulr1.
+ nra.
Qed.

Lemma Rpower_a_c_div_eq_1 (i : 'I_3) (h:R): (0 < h)%Re ->
  forall i, Rpower (Re (a 3 h) * / Re (c 3 h))
                    (INR i + 1 - 1 * / 2)  = 1%Re.
Proof.
intros.
intros. assert ((Re (a 3 h) * / Re (c 3 h))%Re = 1%Re).
{ rewrite a_eq_c.
    + rewrite Rinv_r.
      - by [].
      - rewrite /c. rewrite !mxE. rewrite !big_ord_recr //= !big_ord0.
        rewrite invmx_A1_J.
        * rewrite !mxE.
          assert ((widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max)) = 0).
          { by apply /eqP. } rewrite H0.
          assert ( (widen_ord (leqnSn 2) ord_max) = 1).
          { by apply /eqP. } rewrite H1.
          assert (widen_ord (leqnSn 3) 0 = 0). { by apply /eqP. } rewrite !H2.
          assert (widen_ord (leqnSn 3) 1 = 1). { by apply /eqP. } rewrite !H3.
          assert (widen_ord (leqnSn 3) ord_max = 2). { by apply /eqP. } rewrite !H4.
          assert (0%N == 0%N :> nat = true). { by []. } rewrite !H5.
          assert (1%N == 1%N :> nat = true). { by []. } rewrite !H6.
          assert (@ord_max 2 == @ord_max 2 :> nat = true). {  by []. } rewrite !H7 //=.
          assert ((1 %% 4)%N = 1%N). { by []. } rewrite !H8 //=.
          rewrite inordK //=. rewrite !mulr0 !mulr1 add0r. rewrite !mul0r !addr0 //=.
          rewrite Rmult_1_r.
          assert ((0 == @inord 3 1) = false).
          { assert (@inord 3 1 = 1). {  apply (@inord_val 3 1). }
            by rewrite H9.
          } rewrite H9 //= mulr0n subr0. rewrite -!RoppE -!RmultE.
          assert ((- (- h ^+ 2 * 2^-1 * (1 / (h * (h * 1)))))%Re =
                  ((h ^+ 2 * 2^-1 * (1 / (h * (h * 1)))))%Re). { nra. }
          rewrite H10.
          assert (((h ^+ 2 * 2^-1 * (1 / (h * (h * 1)))))%Re = (/2)%Re).
          { rewrite expr2. rewrite -RmultE. rewrite !Rmult_1_r.
            assert ( (h * h * 2^-1 * (1 / (h * h)))%Re = (((h*h) * / (h*h)) * 2^-1)%Re).
            { nra. } rewrite H11. rewrite Rinv_r.
            + rewrite Rmult_comm Rmult_1_r. rewrite -div1r. rewrite -RdivE.
              - assert ((1 / 2)%Re = (/2)%Re). { nra. } by rewrite H12.
              - by [].
            + nra.
          } rewrite H11. nra.
        * nra.
    + nra.
} rewrite H0. apply rpower_1.
Qed.


Lemma eigen_system (i : 'I_3) (h:R): (0 < h)%Re ->
  let S_mat := RtoC_mat
           (oppmx
              (invmx (A1_J 2 h) *m A2_J 2 h)) in
  (RtoC_vec
   (Eigen_vec i 2 (Re (a 3 h)) (Re (b 3 h))
      (Re (c 3 h))))^T *m S_mat =
  lambda_J i 2 h *:
  (RtoC_vec
     (Eigen_vec i 2 (Re (a 3 h)) (Re (b 3 h))
        (Re (c 3 h))))^T.
Proof.
intros.
apply matrixP. unfold eqrel. intros. rewrite !mxE.
simpl. rewrite !big_ord_recr //= big_ord0 add0r.
assert (forall i, Rpower (Re (a 3 h) * / Re (c 3 h))
                    (INR i + 1 - 1 * / 2)  = 1%Re).
{ by apply Rpower_a_c_div_eq_1. } rewrite H0.
assert ((widen_ord (leqnSn 2) (widen_ord (leqnSn 1) ord_max)) = 0).
{ by apply /eqP. } rewrite H1.
assert ( (widen_ord (leqnSn 2) ord_max) = 1).
{ by apply /eqP. } rewrite H2. rewrite mulr1.
rewrite !mxE. rewrite !H0. rewrite !mulr1.
rewrite !big_ord_recr //= !big_ord0.
rewrite !H1 !H2. rewrite !mxE.
rewrite invmx_A1_J.
+ assert (1%N == 1%N :> nat = true). { by []. } rewrite H3.
  assert (@ord_max 2 == @ord_max 2 :> nat = true). {  by []. } rewrite H4.
  rewrite /lambda_J.
  assert (0%N == 0%N :> nat = true). { by []. } rewrite H5.
  rewrite !mxE //=.
  rewrite !mulr0 !mul0r.
  rewrite !addr0 !add0r.
  assert ((1 %% 3)%N = 1%N). { by []. } rewrite H6.
  assert ((y < 3)%N). { by apply ltn_ord. }
  rewrite leq_eqVlt in H7.
  assert ((y == 2) \/ (y < 2)%N). { by apply /orP. }
  destruct H8.
  - assert (y = 2). { by apply /eqP. } rewrite H9 //=.
    rewrite !Rmult_0_r. rewrite !mulr1. rewrite !mulr0n !mulr1n.
    rewrite !subr0. rewrite !mulr0.
    assert (((1 / (h * (h * 1)) * -2)%Re - (1 / (h * (h * 1)) * -2)%Re)%Re = 0%Re).
    { nra. } rewrite -RminusE. rewrite H10 //=. rewrite !mulr0.
    simpc. apply /eqP. rewrite eq_complex //=. apply /andP.
    split.
    * apply /eqP. rewrite /RtoC.
      assert (b 2 h = (Re (b 2 h) +i* Im (b 2 h))%C).
      { by rewrite -C_destruct. } rewrite H11.
      assert (sqrtc (p 2 h) = (Re (sqrtc (p 2 h)) +i* Im (sqrtc (p 2 h)))%C).
      { by rewrite -C_destruct. } rewrite H12. simpc. rewrite //=.
      rewrite p_destruct //=. rewrite sqrt_p_evals.
      ++ rewrite /b. rewrite !mxE. rewrite !big_ord_recr //= !big_ord0.
         rewrite invmx_A1_J.
         --  rewrite !mxE //=.
             rewrite !Rmult_0_r. rewrite !mulr1. rewrite !mulr0n !mulr1n.
             rewrite !subr0. rewrite !mulr0.
             assert (((1 / (h * (h * 1)) * -2)%Re - (1 / (h * (h * 1)) * -2)%Re)%Re = 0%Re).
             { nra. } rewrite -RminusE. rewrite H10 //=. rewrite !mulr0 !mul0r !addr0.
             rewrite oppr0 add0r.
             rewrite -!RmultE. rewrite Rmult_assoc. rewrite -RplusE.
             assert (((1 + 1) * (1 / 2) *
                         cos ((succn i)%:R * PI * / 4%:R) *
                         (sqrt (2 / (1 + 1 + 1 + 1)) *
                          sin
                            ((1 + 1 + 1) * INR (i + 1) * PI *
                             / (1 + 1 + 1 + 1))))%Re =
                       (sqrt (2 / (1 + 1 + 1 + 1)) *
                         ( cos ((succn i)%:R * PI * / 4%:R) *
                            sin ((1 + 1 + 1) * INR (i + 1) * PI * / (1 + 1 + 1 + 1))))%Re).
             { nra. } rewrite H14. apply Rmult_eq_compat_l.
             assert ( (((1 + 1 + 1) * INR (i + 1) * PI * / (1 + 1 + 1 + 1)))%Re =
                        ((3 * INR (i+1) *PI)/ 4)%Re).
             { nra. } rewrite H15.
             assert (((1 + 1) * INR (i + 1) * PI */ (1 + 1 + 1 + 1))%Re =
                      ((2 * INR (i+1) * PI) /4)%Re).
             { nra. } rewrite H16.
             assert (((succn i)%:R * PI * / 4%:R)%Re= ((INR (i+1) * PI) / 4)%Re).
             { assert (4%:R  = INR 4 :> R). { by rewrite inr_to_R. } rewrite H17.
               assert ((succn i)%:R  = INR (i + 1)). { by rewrite addn1 inr_to_R. } rewrite H18.
               assert (INR 4 = 4%Re). { simpl. nra. } rewrite H19. by [].
             } rewrite H17.
             assert (((h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1)))%Re = (/2)%Re).
             { rewrite expr2. rewrite -RmultE. rewrite !Rmult_1_r.
               assert ( (h * h * 2^-1 * (1 / (h * h)))%Re = (((h*h) * / (h*h)) * 2^-1)%Re).
               { nra. } rewrite H18. rewrite Rinv_r.
               + rewrite Rmult_comm Rmult_1_r. rewrite -div1r. rewrite -RdivE.
                 - assert ((1 / 2)%Re = (/2)%Re). { nra. } by rewrite H19.
                 - by [].
               + nra.
             } rewrite H18.
             assert ((cos (INR (i + 1) * PI / 4) * sin (3 * INR (i + 1) * PI / 4))%Re =
                     ((2 * (cos (INR (i + 1) * PI / 4) *sin (3 * INR (i + 1) * PI / 4)))%Re * /2)%Re).
             { nra. } rewrite H19.
             assert (cos (INR (i + 1) * PI / 4) = cos ( ((4 * INR (i + 1) * PI / 4) - (2 *INR (i + 1) * PI / 4))/2)).
             { assert ( (((4 * INR (i + 1) * PI / 4) - (2 *INR (i + 1) * PI / 4))/2)%Re =
                          (INR (i + 1) * PI / 4)%Re). { nra. } by rewrite H20.
             } rewrite H20.
             assert (sin (3 * INR (i + 1) * PI / 4) = sin ( ((4 * INR (i + 1) * PI / 4) + (2 *INR (i + 1) * PI / 4))/2)).
             { assert ( (((4 * INR (i + 1) * PI / 4) + (2 *INR (i + 1) * PI / 4))/2)%Re =
                          (3 * INR (i + 1) * PI / 4)%Re). { nra. } by rewrite H21.
             } rewrite H21. rewrite -Rmult_assoc. rewrite -form3.
             assert (sin (4 * INR (i + 1) * PI / 4) = 0%Re).
             { assert ((4 * INR (i + 1) * PI / 4)%Re = (INR (i+1) * PI)%Re).
               { nra. } rewrite H22.
               apply sin_eq_0_1. exists (Z.of_nat (i+1)).
               by rewrite INR_IZR_INZ.
             } rewrite H22. nra.
         -- by [].
      ++ by [].
      ++ by [].
    * rewrite Im_complex_prod //=. rewrite mulr0 add0r. rewrite Im_add//=.
      rewrite Im_b_0 add0r. rewrite !Im_complex_prod //=. rewrite !addr0 !mulr0.
      rewrite mul0r addr0 add0r. rewrite Im_p_sqrt_0.
      ++ by rewrite mulr0 !mul0r.
      ++ by [].
      ++ by [].
  - rewrite leq_eqVlt in H8.
    assert ((y == 1) \/ (y < 1)%N). { by apply /orP. } destruct H9.
    * assert (y = 1). { by apply /eqP. } rewrite H10 //=.
      rewrite !mulr1. rewrite !mulr0n !mulr1n.
      rewrite !subr0.
      assert (((1 / (h * (h * 1)) * -2)%Re - (1 / (h * (h * 1)) * -2)%Re)%Re = 0%Re).
      { nra. } rewrite -RminusE. rewrite H11 //=. rewrite !mulr0.
      simpc. apply /eqP. rewrite eq_complex //=. apply /andP. split.
      ++ rewrite /b. rewrite !mxE. rewrite !big_ord_recr //= !big_ord0.
         rewrite invmx_A1_J.
         --  rewrite !mxE //=.
             rewrite !Rmult_0_r. rewrite !mulr1. rewrite !mulr0n !mulr1n.
             rewrite !subr0. rewrite !mulr0.
             assert (((1 / (h * (h * 1)) * -2)%Re - (1 / (h * (h * 1)) * -2)%Re)%Re = 0%Re).
             { nra. } rewrite -RminusE. rewrite H12 //=. rewrite !mulr0 !mul0r !addr0.
             rewrite oppr0 add0r.
             rewrite -!RmultE. rewrite Rmult_assoc. rewrite -RplusE.
             rewrite !Re_complex_prod //=. rewrite mulr0 !addr0 mul0r !subr0 //=.
             rewrite !Im_complex_prod //=. rewrite mulr0  !subr0 //=.
             assert (((h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1)))%Re = (/2)%Re).
             { rewrite expr2. rewrite -RmultE. rewrite !Rmult_1_r.
               assert ( (h * h * 2^-1 * (1 / (h * h)))%Re = (((h*h) * / (h*h)) * 2^-1)%Re).
               { nra. } rewrite H13. rewrite Rinv_r.
               + rewrite Rmult_comm Rmult_1_r. rewrite -div1r. rewrite -RdivE.
                 - assert ((1 / 2)%Re = (/2)%Re). { nra. } by rewrite H14.
                 - by [].
               + nra.
             } rewrite H13.
             assert ((sqrt (2 / (1 + 1 + 1 + 1)) *
                       (sin
                          ((0 + 1) * INR (i + 1) * PI *
                           / (1 + 1 + 1 + 1)) * / 2) +
                       sqrt (2 / (1 + 1 + 1 + 1)) *
                       sin
                         ((1 + 1 + 1) * INR (i + 1) * PI *
                          / (1 + 1 + 1 + 1)) * / 2)%Re =
                      (sqrt (2 / (1 + 1 + 1 + 1)) *
                        ((sin
                          ((0 + 1) * INR (i + 1) * PI *
                           / (1 + 1 + 1 + 1)) + sin
                         ((1 + 1 + 1) * INR (i + 1) * PI *
                          / (1 + 1 + 1 + 1))) * /2))%Re).
            { nra. } rewrite H14. clear H14.
            rewrite p_destruct //=. rewrite -!RmultE -!RplusE.
            * assert (((1 + 1) * sqrt (Re (p 2 h)) *
                         cos ((succn i)%:R * PI * / 4%:R) *
                         (sqrt (2 / (1 + 1 + 1 + 1)) *
                          sin
                            ((1 + 1) * INR (i + 1) * PI *
                             / (1 + 1 + 1 + 1))))%Re =
                       (sqrt (2 / (1 + 1 + 1 + 1)) *
                          ((1 + 1) * sqrt (Re (p 2 h)) *
                              cos ((succn i)%:R * PI * / 4%:R) * sin
                             ((1 + 1) * INR (i + 1) * PI *
                              / (1 + 1 + 1 + 1))))%Re). { nra. } rewrite  H14.
              clear H14. apply /eqP. apply Rmult_eq_compat_l.
              rewrite /p /a /c !mxE //=. rewrite !big_ord_recr //= !big_ord0.
              rewrite invmx_A1_J.
              ++ rewrite !H1 !H2. rewrite !mxE. rewrite !H3 !H5 //=.
                 rewrite H6.
                 assert (0%N == @inord 2 1 :> nat = false).
                 { by rewrite inordK. } rewrite !H14.
                 assert (1%N == @inord 2 1 :> nat = true).
                 { by rewrite inordK. } rewrite !H15.
                 assert (2%N == @inord 2 1 :> nat = false).
                 { by rewrite inordK. } rewrite !H16.
                 assert ((@inord 2 1 - 0)%N == 1%N :> nat = true).
                 { by rewrite inordK. } rewrite !H17.
                 assert ((2 - @inord 2 1)%N == 1%N = true).
                 { by rewrite inordK. } rewrite !H18.
                 assert ((ord_max == @inord 2 1) = false).
                 { by [].  } rewrite !H19 //=.
                 assert ((0 == @inord 2 1) = false). { by []. } rewrite !H20.
                 rewrite eq_sym in H20. rewrite !H20 //=.
                 assert (@inord 2 1 == @ord_max 2 = false).
                 { assert (@inord 2 1 = 1). {  apply (@inord_val 2 1). }
                   rewrite H21.
                   assert (@ord_max 2 = 2). { by apply /eqP. } rewrite H22.
                   by [].
                 } rewrite H21.
                 assert (@inord 2 1 = 1). {  apply (@inord_val 2 1). }
                 rewrite H22 //=. rewrite !mulr0n !mulr1n !mulr0 !mul0r !addr0 !add0r !subr0.
                 rewrite -!RmultE -!RoppE.
                 -- assert ((-
                              (- h ^+ 2 * 2^-1 * 1 *
                               (1 / (h * (h * 1)) * 1)) *
                              -
                              (- h ^+ 2 * 2^-1 * 1 *
                               (1 / (h * (h * 1)) * 1)))%Re =
                             ((h ^+ 2 * 2^-1 * 1 *
                               (1 / (h * (h * 1)) * 1)) * (h ^+ 2 * 2^-1 * 1 *
                               (1 / (h * (h * 1)) * 1)))%Re). { nra. } rewrite H23. clear H23.
                    rewrite sqrt_square.
                    *  assert (((h ^+ 2 * 2^-1 * 1* (1 / (h * (h * 1)) * 1)))%Re = (/2)%Re).
                       { rewrite expr2. rewrite -RmultE. rewrite !Rmult_1_r.
                         assert ( (h * h * 2^-1 * (1 / (h * h)))%Re = (((h*h) * / (h*h)) * 2^-1)%Re).
                         { nra. } rewrite H23. rewrite Rinv_r.
                         + rewrite Rmult_comm Rmult_1_r. rewrite -div1r. rewrite -RdivE.
                           - assert ((1 / 2)%Re = (/2)%Re). { nra. } by rewrite H24.
                           - by [].
                         + nra.
                       } rewrite H23.
                       assert (((1 + 1) * / 2 *
                                   cos ((succn i)%:R * PI * / 4%:R) *
                                   sin
                                     ((1 + 1) * INR (i + 1) * PI *
                                      / (1 + 1 + 1 + 1)))%Re =
                                (cos ((succn i)%:R * PI * / 4%:R) *
                                   sin
                                     ((1 + 1) * INR (i + 1) * PI *
                                      / (1 + 1 + 1 + 1)))%Re).
                       { nra. } rewrite H24. clear H23 H24.
                       assert (sin ((0 + 1) * INR (i + 1) * PI */ (1 + 1 + 1 + 1)) =
                                sin ( (INR (i+1) * PI) / 4)).
                       { assert (((0 + 1) * INR (i + 1) * PI */ (1 + 1 + 1 + 1))%Re =
                                    ( (INR (i+1) * PI) / 4)%Re).
                         { nra. } by rewrite H23.
                       } rewrite H23. clear H23.
                       assert (sin ((1 + 1 + 1) * INR (i + 1) * PI * / (1 + 1 + 1 + 1)) =
                                 sin ( (3 * INR (i+1) * PI) / 4)).
                       { assert (((1 + 1 + 1) * INR (i + 1) * PI * / (1 + 1 + 1 + 1))%Re =
                                    ( (3 * INR (i+1) * PI) / 4)%Re).
                         { nra. } by rewrite H23.
                       } rewrite H23. clear H23. rewrite Rplus_comm. rewrite form3.
                       assert (((3 * INR (i + 1) * PI / 4 - INR (i + 1) * PI / 4) / 2)%Re =
                                (( INR (i+1) * PI) / 4)%Re).
                       { nra. } rewrite H23. clear H23.
                       assert (((3 * INR (i + 1) * PI / 4 + INR (i + 1) * PI / 4) / 2)%Re =
                                ((2 * INR (i+1) * PI)/4)%Re). { nra. } rewrite H23. clear H23.
                       assert ((2 * cos (INR (i + 1) * PI / 4) *
                                  sin (2 * INR (i + 1) * PI / 4) * / 2)%Re =
                                (cos (INR (i + 1) * PI / 4) * sin (2 * INR (i + 1) * PI / 4))%Re).
                       { nra. } rewrite H23. clear H23.
                       assert (((succn i)%:R * PI * / 4%:R)%Re= ((INR (i+1) * PI) / 4)%Re).
                       { assert (4%:R  = INR 4 :> R). { by rewrite inr_to_R. } rewrite H23.
                         assert ((succn i)%:R  = INR (i + 1)). { by rewrite addn1 inr_to_R. } rewrite H24.
                         assert (INR 4 = 4%Re). { simpl. nra. } rewrite H25. by [].
                       } rewrite H23. clear H23.
                       assert ( ((1 + 1) * INR (i + 1) * PI * / (1 + 1 + 1 + 1))%Re =
                                  (2 * INR (i + 1) * PI / 4)%Re). { nra. } by rewrite H23.
                    * nra.
                  -- nra.
                ++ nra.
             *  rewrite Im_complex_prod //=. rewrite mulr0 add0r. rewrite Im_add//=.
                rewrite Im_b_0 add0r. rewrite !Im_complex_prod //=. rewrite !addr0 !mulr0.
                rewrite mul0r addr0 add0r. rewrite Im_p_sqrt_0.
                ++ by rewrite mulr0 !mul0r.
                ++ by [].
                ++ by [].
    * rewrite ltnS in H9. rewrite leqn0 in H9.
      assert (y = 0). { by apply /eqP. } rewrite H10 //=.
      rewrite !mulr1. rewrite !mulr0n !mulr1n.
      rewrite !subr0.
      assert (((1 / (h * (h * 1)) * -2)%Re - (1 / (h * (h * 1)) * -2)%Re)%Re = 0%Re).
      { nra. } rewrite -RminusE. rewrite H11 //=. rewrite !mulr0.
      simpc. apply /eqP. rewrite eq_complex //=. apply /andP. split.
      ++ rewrite /b. rewrite !mxE. rewrite !big_ord_recr //= !big_ord0.
         rewrite invmx_A1_J.
         rewrite !mxE. rewrite !H1 !H2 //=.
            rewrite !mulr1n !mulr0n !mulr0 !mul0r. rewrite !Rmult_0_r.
            assert (((1 / (h * (h * 1)) * -2)%Re - (1 / (h * (h * 1)) * -2)%Re)%Re = 0%Re).
            { nra. } rewrite -RminusE. rewrite H12 //=. rewrite !mulr0 !addr0.
            rewrite oppr0. rewrite add0r. rewrite !Re_complex_prod //=.
            rewrite mulr0 //=. rewrite addr0 mul0r. rewrite !subr0.
            rewrite !Im_complex_prod //=. rewrite mulr0 subr0.
            rewrite p_destruct //=. rewrite -!RmultE -!RplusE.
            * rewrite /p /a /c !mxE //=. rewrite !big_ord_recr //= !big_ord0.
              rewrite invmx_A1_J.
              ++ rewrite !H1 !H2 //=. rewrite !mxE //=. rewrite H6.
                 assert (0%N == @inord 2 1 :> nat = false).
                 { by rewrite inordK. } rewrite !H13.
                 assert (1%N == @inord 2 1 :> nat = true).
                 { by rewrite inordK. } rewrite !H14.
                 assert (2%N == @inord 2 1 :> nat = false).
                 { by rewrite inordK. } rewrite !H15.
                 assert ((@inord 2 1 - 0)%N == 1%N :> nat = true).
                 { by rewrite inordK. } rewrite !H16.
                 assert ((2 - @inord 2 1)%N == 1%N = true).
                 { by rewrite inordK. } rewrite !H17.
                 assert ((ord_max == @inord 2 1) = false).
                 { by [].  } rewrite !H18 //=.
                 assert ((0 == @inord 2 1) = false). { by []. } rewrite !H19.
                 rewrite eq_sym in H19. rewrite !H19 //=.
                 assert (@inord 2 1 == @ord_max 2 = false).
                 { assert (@inord 2 1 = 1). {  apply (@inord_val 2 1). }
                   rewrite H20.
                   assert (@ord_max 2 = 2). { by apply /eqP. } rewrite H21.
                   by [].
                 } rewrite H20.
                 assert (@inord 2 1 = 1). {  apply (@inord_val 2 1). }
                 rewrite H21 //=. rewrite !mulr0n !mulr1n !mulr0 !mul0r !addr0 !add0r !subr0.
                 rewrite -!RmultE -!RoppE.
                 -- assert ((-
                              (- h ^+ 2 * 2^-1 * 1 *
                               (1 / (h * (h * 1)) * 1)) *
                              -
                              (- h ^+ 2 * 2^-1 * 1 *
                               (1 / (h * (h * 1)) * 1)))%Re =
                             ((h ^+ 2 * 2^-1 * 1 *
                               (1 / (h * (h * 1)) * 1)) * (h ^+ 2 * 2^-1 * 1 *
                               (1 / (h * (h * 1)) * 1)))%Re). { nra. } rewrite H22. clear H22.
                    rewrite sqrt_square.
                    *  assert (((h ^+ 2 * 2^-1 * 1* (1 / (h * (h * 1)) * 1)))%Re = (/2)%Re).
                       { rewrite expr2. rewrite -RmultE. rewrite !Rmult_1_r.
                         assert ( (h * h * 2^-1 * (1 / (h * h)))%Re = (((h*h) * / (h*h)) * 2^-1)%Re).
                         { nra. } rewrite H22. rewrite Rinv_r.
                         + rewrite Rmult_comm Rmult_1_r. rewrite -div1r. rewrite -RdivE.
                           - assert ((1 / 2)%Re = (/2)%Re). { nra. } by rewrite H23.
                           - by [].
                         + nra.
                       } rewrite H22.
                       assert ((h ^+ 2 * 2^-1 * (1 / (h * (h * 1)) * 1))%Re =
                                (h ^+ 2 * 2^-1 * 1 *(1 / (h * (h * 1)) * 1))%Re).
                       { nra. } rewrite H23 H22.
                       assert (((1 + 1) * / 2 *
                                 cos ((succn i)%:R * PI * / 4%:R) *
                                 (sqrt (2 / (1 + 1 + 1 + 1)) *
                                  sin
                                    ((0 + 1) * INR (i + 1) * PI *
                                     / (1 + 1 + 1 + 1))))%Re =
                                (sqrt (2 / (1 + 1 + 1 + 1)) *
                                   ((1 + 1) * / 2 * cos ((succn i)%:R * PI * / 4%:R) * sin
                                    ((0 + 1) * INR (i + 1) * PI *
                                     / (1 + 1 + 1 + 1))))%Re).
                        { nra. } rewrite H24. rewrite Rmult_assoc.
                        apply /eqP. apply Rmult_eq_compat_l.
                        assert (((1 + 1) * / 2 *
                                   cos ((succn i)%:R * PI * / 4%:R) *
                                   sin
                                     ((0 + 1) * INR (i + 1) * PI *
                                      / (1 + 1 + 1 + 1)))%Re =
                                (cos ((succn i)%:R * PI * / 4%:R) *
                                   sin
                                     ((0 + 1) * INR (i + 1) * PI *
                                      / (1 + 1 + 1 + 1)))%Re).
                       { nra. } rewrite H25. clear H23 H24 H25.
                       assert (((succn i)%:R * PI * / 4%:R)%Re= ((INR (i+1) * PI) / 4)%Re).
                       { assert (4%:R  = INR 4 :> R). { by rewrite inr_to_R. } rewrite H23.
                         assert ((succn i)%:R  = INR (i + 1)). { by rewrite addn1 inr_to_R. } rewrite H24.
                         assert (INR 4 = 4%Re). { simpl. nra. } rewrite H25. by [].
                       } rewrite H23. clear H23.
                       assert (sin ((1 + 1) * INR (i + 1) * PI * / (1 + 1 + 1 + 1)) =
                                  sin ((2 * INR (i+1) * PI) / 4)).
                       { assert (((1 + 1) * INR (i + 1) * PI * / (1 + 1 + 1 + 1))%Re =
                                  ((2 * INR (i+1) * PI) / 4)%Re).
                          { nra. } by rewrite H23.
                       } rewrite H23.
                       assert (((0 + 1) * INR (i + 1) * PI * / (1 + 1 + 1 + 1))%Re =
                                (INR (i+1) * PI / 4)%Re).
                       { nra. } rewrite H24.
                       assert ((cos (INR (i + 1) * PI / 4) *
                                  sin (INR (i + 1) * PI / 4))%Re  =
                                ((2  * sin (INR (i + 1) * PI / 4) * cos (INR (i + 1) * PI / 4)) * /2)%Re).
                       { nra. } rewrite H25. rewrite -sin_2a.
                       assert ((2 * (INR (i + 1) * PI / 4))%Re = (2 * INR (i + 1) * PI / 4)%Re).
                       { nra. } by rewrite H26.
                     * assert (((h ^+ 2 * 2^-1 * 1* (1 / (h * (h * 1)) * 1)))%Re = (/2)%Re).
                       { rewrite expr2. rewrite -RmultE. rewrite !Rmult_1_r.
                         assert ( (h * h * 2^-1 * (1 / (h * h)))%Re = (((h*h) * / (h*h)) * 2^-1)%Re).
                         { nra. } rewrite H22. rewrite Rinv_r.
                         + rewrite Rmult_comm Rmult_1_r. rewrite -div1r. rewrite -RdivE.
                           - assert ((1 / 2)%Re = (/2)%Re). { nra. } by rewrite H23.
                           - by [].
                         + nra.
                       } rewrite H22. nra.
                  -- nra.
               ++ nra.
         ++ rewrite Im_complex_prod //=. rewrite mulr0 add0r. rewrite Im_add//=.
            rewrite Im_b_0 add0r. rewrite !Im_complex_prod //=. rewrite !addr0 !mulr0.
            rewrite mul0r addr0 add0r. rewrite Im_p_sqrt_0.
            -- by rewrite mulr0 !mul0r.
            -- by [].
            -- by [].
+ by [].
Qed.


Lemma lambda_J_is_an_eigenvalue:
  forall (h:R),
  (0 < h)%Re ->
  let S_mat := RtoC_mat
           (oppmx
              (invmx (A1_J 2 h) *m A2_J 2 h)) in
  (forall i: 'I_3,
      @eigenvalue (complex_fieldType _) 3%N S_mat (lambda_J i 2%N h)).
Proof.
intros. apply /eigenvalueP.
  exists (RtoC_vec (Eigen_vec i 2%N (Re (a 3%N h)) (Re (b 3%N h)) (Re (c 3%N h))))^T.
  - by apply eigen_system.
  - apply /rV0Pn. exists 0. rewrite !mxE.
    assert (Rpower (Re (a 3 h) * / Re (c 3 h)) (INR 0 + 1 - 1 * / 2) = 1%Re).
    { by apply Rpower_a_c_div_eq_1. } rewrite H0.
    rewrite eq_complex //=. apply /nandP.
    left. rewrite mulr1. apply /eqP.
    apply Rmult_integral_contrapositive.
    split.
    * assert ((0 < sqrt (2 / (1 + 1 + 1 + 1)))%Re ->
                    sqrt (2 / (1 + 1 + 1 + 1)) <> 0%Re). { nra. } apply H1.
      apply sqrt_lt_R0.
      nra.
    * assert (((0 + 1))%Re = 1%Re). { nra. } rewrite H1.
      assert ((1 * INR (i + 1) * PI * / (1 + 1 + 1 + 1))%Re =
              (INR (i + 1) * PI * /4)%Re). { nra. } rewrite H2.
      assert ( (0 < sin (INR (i + 1) * PI * / 4))%Re ->
              sin (INR (i + 1) * PI * / 4) <> 0%Re).
      { nra. } apply H3. apply sin_gt_0.
      + apply Rmult_lt_0_compat.
        ++ apply Rmult_lt_0_compat.
           -- apply lt_0_INR. apply /ssrnat.ltP. by rewrite addn1.
           -- apply PI_RGT_0.
        ++ nra.
      + assert (PI = (1 * PI)%Re). { nra. } rewrite H4.
        assert ((INR (i + 1) * (1 * PI) * / 4)%Re =
                  ((INR (i+1) * /4) * PI)%Re).
        { nra. } rewrite H5.
        apply Rmult_lt_compat_r.
        - apply PI_RGT_0.
        - assert ((INR (i + 1)  < 4 )%Re -> (INR (i + 1) * / 4 < 1)%Re).
          { nra. } apply H6. assert (INR 4 = 4%Re). { simpl. nra. }
          rewrite -H7. apply lt_INR. apply /ssrnat.ltP.
          assert ((i < 3)%N). { apply ltn_ord. }
          assert (4%N = (3 + 1)%N). { by []. } rewrite H9. by rewrite ltn_add2r.
Qed.


Theorem Jacobi_converges:
  forall (b: 'cV[R]_3) (h:R),
  (0 < h)%Re ->
  let A := (Ah 2%N h) in
  let x := (invmx A) *m b in
    (forall x0: 'cV[R]_3,
        is_lim_seq (fun m:nat => vec_norm
          (addmx (X_m m.+1 x0 b (A1_J 2%N h) (A2_J 2%N h))
                  (oppmx x))) 0%Re).
Proof.
intros.
apply iter_convergence.
+ rewrite /A0. by apply Ah_is_invertible.
+ by apply A1_invertible.
+ apply Ah_J_split.
+ intros. rewrite Lambda_eq. by apply eig_less_than_1.
Qed.

