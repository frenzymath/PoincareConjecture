import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology Bundle
open Filter

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private lemma fderiv_bilinear_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : E → E →L[ℝ] E →L[ℝ] F} {x : E}
    (hA : DifferentiableAt ℝ A x) (u v w : E) :
    fderiv ℝ (fun y ↦ A y v w) x u = fderiv ℝ A x u v w := by
  have h := (hA.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply
    (hasFDerivAt_const w x)
  simpa using congrArg (fun L ↦ L u) h.fderiv

private lemma fderiv_metric_apply (x u v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y ↦ g.inner y v w) x u =
      fderiv ℝ g.euclideanCoefficients x u v w :=
  fderiv_bilinear_apply ((g.contDiffAt_euclideanCoefficients x).differentiableAt
    (by simp)) u v w

private lemma metric_deriv_symm (x u v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ g.euclideanCoefficients x u v w =
      fderiv ℝ g.euclideanCoefficients x u w v := by
  rw [← fderiv_metric_apply, ← fderiv_metric_apply]
  congr 2
  exact funext fun y ↦ g.symm y v w

private lemma fderiv_metric_deriv_apply (x a u v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y ↦ fderiv ℝ g.euclideanCoefficients y u v w) x a =
      fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a u v w := by
  have hG := ((g.contDiffAt_euclideanCoefficients x).fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have h := ((hG.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  simpa using congrArg (fun L ↦ L a) h.fderiv

private lemma metric_second_deriv_symm (x a u v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a u v w =
      fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a u w v := by
  rw [← fderiv_metric_deriv_apply, ← fderiv_metric_deriv_apply]
  congr 2
  exact funext fun y ↦ metric_deriv_symm y u v w

private lemma metric_second_deriv_comm (x a u v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a u v w =
      fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x u a v w := by
  have h := (g.contDiffAt_euclideanCoefficients x).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun L ↦ L v w) (h.eq a u)

private lemma inner_euclideanConnection (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    g.inner x (D.euclideanConnection u v x) w = (2⁻¹ : ℝ) *
      (fderiv ℝ g.euclideanCoefficients x u v w +
        fderiv ℝ g.euclideanCoefficients x v w u -
        fderiv ℝ g.euclideanCoefficients x w u v) := by
  have h := D.inner_connection_const x u v w
  rw [fderiv_metric_apply, fderiv_metric_apply, fderiv_metric_apply] at h
  change 2 * g.inner x (D.euclideanConnection u v x) w = _ at h
  linarith

lemma inner_fderiv_euclideanConnection (D : LeviCivitaData g)
    (x a u v w : EuclideanSpace ℝ (Fin n)) :
    g.inner x (fderiv ℝ (D.euclideanConnection u v) x a) w =
      (2⁻¹ : ℝ) *
        (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a u v w +
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a v w u -
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a w u v) -
      fderiv ℝ g.euclideanCoefficients x a (D.euclideanConnection u v x) w := by
  have hG := (g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp)
  have hC := (D.contDiffAt_euclideanConnection x u v).differentiableAt (by simp)
  have hG' := ((g.contDiffAt_euclideanCoefficients x).fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hd (b c d : EuclideanSpace ℝ (Fin n)) :
      DifferentiableAt ℝ (fun y ↦ fderiv ℝ g.euclideanCoefficients y b c d) x :=
    ((hG'.clm_apply (differentiableAt_const b)).clm_apply
      (differentiableAt_const c)).clm_apply (differentiableAt_const d)
  have heq := congrArg (fun f : EuclideanSpace ℝ (Fin n) → ℝ ↦ fderiv ℝ f x a)
    (funext fun y ↦ D.inner_euclideanConnection y u v w)
  have hleft := ((hG.hasFDerivAt.clm_apply hC.hasFDerivAt).clm_apply
    (hasFDerivAt_const w x)).fderiv
  change fderiv ℝ (fun y ↦ g.inner y (D.euclideanConnection u v y) w)
    x = _ at hleft
  rw [hleft, fderiv_const_mul ((hd u v w).fun_add (hd v w u) |>.fun_sub (hd w u v)),
    fderiv_fun_sub ((hd u v w).fun_add (hd v w u)) (hd w u v),
    fderiv_fun_add (hd u v w) (hd v w u)] at heq
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add, smul_eq_mul] at heq
  rw [fderiv_metric_deriv_apply, fderiv_metric_deriv_apply,
    fderiv_metric_deriv_apply] at heq
  change g.inner x (fderiv ℝ (D.euclideanConnection u v) x a) w +
    fderiv ℝ g.euclideanCoefficients x a (D.euclideanConnection u v x) w = _ at heq
  linarith

lemma curvatureTensor_eq_metric_second_deriv (D : LeviCivitaData g)
    (x u b v c : EuclideanSpace ℝ (Fin n)) :
    D.curvatureTensor x u b v c =
      (2⁻¹ : ℝ) *
        (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x u c b v -
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x u v b c -
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x b c u v +
          fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x b v u c) +
      (-fderiv ℝ g.euclideanCoefficients x u (D.euclideanConnection b c x) v +
        fderiv ℝ g.euclideanCoefficients x b (D.euclideanConnection u c x) v +
        g.inner x (D.euclideanConnection u (D.euclideanConnection b c x) x) v -
        g.inner x (D.euclideanConnection b (D.euclideanConnection u c x) x) v) := by
  unfold curvatureTensor
  rw [D.curvature_eq_euclideanConnection]
  simp only [map_sub, map_add, sub_apply, add_apply]
  rw [D.inner_fderiv_euclideanConnection, D.inner_fderiv_euclideanConnection,
    metric_second_deriv_comm x b u c v, metric_second_deriv_symm x u c v b,
    metric_second_deriv_symm x b c v u]
  ring

private lemma inverseCoefficients_eq_sum_orthonormal (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    g.inverseCoefficients x i j =
      ∑ k, EuclideanSpace.proj i (g.orthonormalBasis x k) *
        EuclideanSpace.proj j (g.orthonormalBasis x k) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := congrArg (fun v : TangentSpace (𝓡 n) x ↦ EuclideanSpace.proj j v)
    ((g.orthonormalBasis x).sum_repr' ((g.inner x).inverse (EuclideanSpace.proj i)))
  have hp (k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      inner ℝ (g.orthonormalBasis x k) ((g.inner x).inverse (EuclideanSpace.proj i)) =
        EuclideanSpace.proj i (g.orthonormalBasis x k) := by
    change g.inner x (g.orthonormalBasis x k) ((g.inner x).inverse (EuclideanSpace.proj i)) = _
    rw [g.symm, (g.inner_isInvertible x).self_apply_inverse]
    rfl
  simpa only [OrthonormalBasis.repr_apply_apply, hp, map_sum, map_smul,
    smul_eq_mul, RiemannianMetric.inverseCoefficients] using h.symm

lemma ricci_eq_sum_inverseCoefficients_curvatureTensor (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    D.ricci x u v = ∑ i, ∑ j, g.inverseCoefficients x i j *
      D.curvatureTensor x u (EuclideanSpace.basisFun (Fin n) ℝ i) v
        (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor x
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h1 (a c d : EuclideanSpace ℝ (Fin n)) :
      Function.update ![u, a, v, c] 1 d = ![u, d, v, c] := by
    ext i; fin_cases i <;> simp
  have h3 (a c d : EuclideanSpace ℝ (Fin n)) :
      Function.update ![u, a, v, c] 3 d = ![u, a, v, d] := by
    ext i; fin_cases i <;> simp
  have hexp (a c : EuclideanSpace ℝ (Fin n)) :
      A ![u, a, v, c] = ∑ i, ∑ j, (a i * c j) * A ![u, b i, v, b j] := by
    have ha := congrArg (A.toLinearMap ![u, a, v, c] 1) (b.toBasis.sum_repr a)
    simp only [map_sum, map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply,
      h1, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      b, EuclideanSpace.basisFun_repr] at ha
    rw [← ha]
    apply Finset.sum_congr rfl
    intro i _
    have hc := congrArg (A.toLinearMap ![u, b i, v, c] 3) (b.toBasis.sum_repr c)
    simp only [map_sum, map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply,
      h3, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      b, EuclideanSpace.basisFun_repr] at hc
    rw [← hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hA' (a c : EuclideanSpace ℝ (Fin n)) :
      D.curvatureTensor x u a v c = A ![u, a, v, c] := hA ![u, a, v, c]
  change (∑ k, D.curvatureTensor x u (g.orthonormalBasis x k) v
    (g.orthonormalBasis x k)) = _
  simp only [hA']
  conv_lhs => arg 2; ext k; rw [hexp]
  simp_rw [inverseCoefficients_eq_sum_orthonormal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  rfl

private lemma harmonic_metric_gauge (D : LeviCivitaData g)
    {x : EuclideanSpace ℝ (Fin n)}
    (hharm : ∀ i : Fin n, D.laplacian (fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x = 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, g.inverseCoefficients x i j *
      (fderiv ℝ g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j) v +
        fderiv ℝ g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ j)
          v (EuclideanSpace.basisFun (Fin n) ℝ i) -
        fderiv ℝ g.euclideanCoefficients x v (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j))) = 0 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h := congrArg (fun w : EuclideanSpace ℝ (Fin n) ↦ g.inner x w v)
    (D.sum_christoffel_inverse_eq_zero_of_harmonic hharm)
  have hexp (i : Fin n) : (g.inner x).inverse (EuclideanSpace.proj i) =
      ∑ j, g.inverseCoefficients x i j • b j := by
    simpa only [b, RiemannianMetric.inverseCoefficients, PiLp.proj_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr] using
      (b.toBasis.sum_repr ((g.inner x).inverse (EuclideanSpace.proj i))).symm
  have hC (a c : EuclideanSpace ℝ (Fin n)) :
      CoordinateExponential.christoffelBilinear g.euclideanCoefficients x a c =
        D.euclideanConnection a c x := by
    exact (D.connection_const_eq_inverse x a c).symm
  simp_rw [hexp, map_sum, map_smul, sum_apply, smul_apply, hC,
    D.inner_euclideanConnection, smul_eq_mul] at h
  simp only [map_zero, zero_apply] at h
  have h' : (2⁻¹ : ℝ) * (∑ i, ∑ j, g.inverseCoefficients x i j *
      (fderiv ℝ g.euclideanCoefficients x (b i) (b j) v +
        fderiv ℝ g.euclideanCoefficients x (b j) v (b i) -
        fderiv ℝ g.euclideanCoefficients x v (b i) (b j))) = 0 := by
    convert h using 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∑ i, ∑ j, g.inverseCoefficients x i j *
      (fderiv ℝ g.euclideanCoefficients x (b i) (b j) v +
        fderiv ℝ g.euclideanCoefficients x (b j) v (b i) -
        fderiv ℝ g.euclideanCoefficients x v (b i) (b j))) = 0
  linarith

lemma sum_metric_second_deriv_gauge_of_harmonic (D : LeviCivitaData g)
    {x : EuclideanSpace ℝ (Fin n)}
    (hharm : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      D.laplacian (fun z : EuclideanSpace ℝ (Fin n) ↦ z i) y = 0)
    (a v : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, g.inverseCoefficients x i j *
      (fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) v +
        fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a
          (EuclideanSpace.basisFun (Fin n) ℝ j) v (EuclideanSpace.basisFun (Fin n) ℝ i) -
        fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a v
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))) =
      -(∑ i, ∑ j, fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x a *
        (fderiv ℝ g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j) v +
          fderiv ℝ g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ j)
            v (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ g.euclideanCoefficients x v (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j))) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let F (i j : Fin n) (y : EuclideanSpace ℝ (Fin n)) :=
    fderiv ℝ g.euclideanCoefficients y (b i) (b j) v +
      fderiv ℝ g.euclideanCoefficients y (b j) v (b i) -
      fderiv ℝ g.euclideanCoefficients y v (b i) (b j)
  have hG' := ((g.contDiffAt_euclideanCoefficients x).fderiv_right
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hd (c d e : EuclideanSpace ℝ (Fin n)) :
      DifferentiableAt ℝ (fun y ↦ fderiv ℝ g.euclideanCoefficients y c d e) x :=
    ((hG'.clm_apply (differentiableAt_const c)).clm_apply
      (differentiableAt_const d)).clm_apply (differentiableAt_const e)
  have hF (i j : Fin n) : DifferentiableAt ℝ (F i j) x :=
    ((hd (b i) (b j) v).fun_add (hd (b j) v (b i))).fun_sub (hd v (b i) (b j))
  have hI (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ g.inverseCoefficients y i j) x :=
    (g.contDiff_inverseCoefficients i j).differentiable (by simp) x
  have heq : (fun y ↦ ∑ i, ∑ j, g.inverseCoefficients y i j * F i j y) =ᶠ[𝓝 x]
      (fun _ ↦ (0 : ℝ)) := hharm.mono fun y hy ↦ D.harmonic_metric_gauge hy v
  have hzero := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ L a)
    heq.fderiv_eq
  rw [fderiv_fun_sum (fun i _ ↦ DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ ↦
    (hI i j).fun_mul (hF i j)))] at hzero
  simp_rw [fderiv_fun_sum (fun j _ ↦ (hI _ j).fun_mul (hF _ j)),
    fderiv_fun_mul (hI _ _) (hF _ _)] at hzero
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, fderiv_const_apply,
    zero_apply] at hzero
  have hFd (i j : Fin n) : fderiv ℝ (F i j) x a =
      fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a (b i) (b j) v +
        fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a (b j) v (b i) -
        fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a v (b i) (b j) := by
    dsimp [F]
    rw [fderiv_fun_sub ((hd (b i) (b j) v).fun_add (hd (b j) v (b i)))
      (hd v (b i) (b j)), fderiv_fun_add (hd (b i) (b j) v) (hd (b j) v (b i))]
    simp only [add_apply, sub_apply, fderiv_metric_deriv_apply]
  simp_rw [hFd, Finset.sum_add_distrib] at hzero
  dsimp [F, b] at hzero
  simpa only [mul_comm] using eq_neg_of_add_eq_zero_left hzero

noncomputable def harmonicRicciQuadratic (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  (∑ i, ∑ j, g.inverseCoefficients x i j *
    (-fderiv ℝ g.euclideanCoefficients x u (D.euclideanConnection (b i) (b j) x) v +
      fderiv ℝ g.euclideanCoefficients x (b i) (D.euclideanConnection u (b j) x) v +
      g.inner x (D.euclideanConnection u (D.euclideanConnection (b i) (b j) x) x) v -
      g.inner x (D.euclideanConnection (b i) (D.euclideanConnection u (b j) x) x) v)) -
  (2⁻¹ : ℝ) * (∑ i, ∑ j,
    (fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x u *
      g.inner x (D.euclideanConnection (b i) (b j) x) v +
    fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x v *
      g.inner x (D.euclideanConnection (b i) (b j) x) u))

theorem ricci_eq_principal_add_harmonicRicciQuadratic (D : LeviCivitaData g)
    {x : EuclideanSpace ℝ (Fin n)}
    (hharm : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      D.laplacian (fun z : EuclideanSpace ℝ (Fin n) ↦ z i) y = 0)
    (u v : EuclideanSpace ℝ (Fin n)) :
    D.ricci x u v = -(2⁻¹ : ℝ) *
      (∑ i, ∑ j, g.inverseCoefficients x i j *
        fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) u v) +
      D.harmonicRicciQuadratic x u v := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let S := fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x
  let T (a c : EuclideanSpace ℝ (Fin n)) :=
    ∑ i, ∑ j, g.inverseCoefficients x i j * S a (b i) (b j) c
  let U (a c : EuclideanSpace ℝ (Fin n)) :=
    ∑ i, ∑ j, g.inverseCoefficients x i j * S a c (b i) (b j)
  let J (a c : EuclideanSpace ℝ (Fin n)) :=
    ∑ i, ∑ j, fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x a *
      g.inner x (D.euclideanConnection (b i) (b j) x) c
  have hswap (a c : EuclideanSpace ℝ (Fin n)) :
      (∑ i, ∑ j, g.inverseCoefficients x i j * S a (b j) c (b i)) = T a c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [g.inverseCoefficients_symm]
    congr 1
    exact metric_second_deriv_symm x a (b i) c (b j)
  have hswap' (a c : EuclideanSpace ℝ (Fin n)) :
      (∑ i, ∑ j, g.inverseCoefficients x i j * S a (b j) (b i) c) = T a c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [g.inverseCoefficients_symm]
  have hU : U v u = U u v := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact metric_second_deriv_comm x v u (b i) (b j)
  have hgauge (a c : EuclideanSpace ℝ (Fin n)) :
      2 * T a c - U a c = -2 * J a c := by
    have h := D.sum_metric_second_deriv_gauge_of_harmonic hharm a c
    change (∑ i, ∑ j, g.inverseCoefficients x i j *
      (S a (b i) (b j) c + S a (b j) c (b i) - S a c (b i) (b j))) = _ at h
    have hK (i j : Fin n) :
        fderiv ℝ g.euclideanCoefficients x (b i) (b j) c +
          fderiv ℝ g.euclideanCoefficients x (b j) c (b i) -
          fderiv ℝ g.euclideanCoefficients x c (b i) (b j) =
            2 * g.inner x (D.euclideanConnection (b i) (b j) x) c := by
      rw [D.inner_euclideanConnection]
      ring
    change (∑ i, ∑ j, g.inverseCoefficients x i j *
      (S a (b i) (b j) c + S a (b j) c (b i) - S a c (b i) (b j))) =
      -(∑ i, ∑ j, fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x a *
        (fderiv ℝ g.euclideanCoefficients x (b i) (b j) c +
          fderiv ℝ g.euclideanCoefficients x (b j) c (b i) -
          fderiv ℝ g.euclideanCoefficients x c (b i) (b j))) at h
    simp only [hK, mul_add, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
    rw [hswap] at h
    have hJ : (∑ i, ∑ j, fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x a *
        (2 * g.inner x (D.euclideanConnection (b i) (b j) x) c)) = 2 * J a c := by
      dsimp [J]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hJ] at h
    change T a c + T a c - U a c = -(2 * J a c) at h
    linarith
  have hlast : (∑ i, ∑ j, g.inverseCoefficients x i j * S (b i) v u (b j)) =
      T v u := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (metric_second_deriv_comm x (b i) v u (b j)).trans
      (metric_second_deriv_symm x v (b i) u (b j))
  rw [D.ricci_eq_sum_inverseCoefficients_curvatureTensor]
  simp_rw [D.curvatureTensor_eq_metric_second_deriv]
  dsimp [harmonicRicciQuadratic]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hhalf (F : Fin n → Fin n → ℝ) :
      (∑ i, ∑ j, g.inverseCoefficients x i j * (2⁻¹ * F i j)) =
        2⁻¹ * (∑ i, ∑ j, g.inverseCoefficients x i j * F i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hhalf]
  change 2⁻¹ * (∑ i, ∑ j, g.inverseCoefficients x i j * S u (b j) (b i) v) -
    2⁻¹ * U u v - 2⁻¹ * _ +
    2⁻¹ * (∑ i, ∑ j, g.inverseCoefficients x i j * S (b i) v u (b j)) + _ = _
  rw [hswap', hlast]
  have hu := hgauge u v
  have hv := hgauge v u
  rw [hU] at hv
  change _ = -(2⁻¹ : ℝ) * _ + (_ - (2⁻¹ * J u v + 2⁻¹ * J v u))
  linarith

theorem laplacian_metric_eq_ricci_of_harmonic (D : LeviCivitaData g)
    {x : EuclideanSpace ℝ (Fin n)}
    (hharm : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      D.laplacian (fun z : EuclideanSpace ℝ (Fin n) ↦ z i) y = 0)
    (u v : EuclideanSpace ℝ (Fin n)) :
    D.laplacian (fun y ↦ g.inner y u v) x =
      -2 * D.ricci x u v + 2 * D.harmonicRicciQuadratic x u v := by
  have hf (y : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ (fun z ↦ g.inner z u v) y :=
    ((g.contDiffAt_euclideanCoefficients y).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const
  have hsecond (a b : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fderiv ℝ (fun y ↦ g.inner y u v)) x a b =
        fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a b u v := by
    have hd := ((hf x).fderiv_right
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
    have happ := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const b x)).fderiv
    have heq : (fun y ↦ fderiv ℝ (fun z ↦ g.inner z u v) y b) =
        (fun y ↦ fderiv ℝ g.euclideanCoefficients y b u v) :=
      funext fun y ↦ fderiv_metric_apply y b u v
    have h := congrArg (fun f : EuclideanSpace ℝ (Fin n) → ℝ ↦ fderiv ℝ f x a) heq
    rw [happ, fderiv_metric_deriv_apply] at h
    simpa using h
  rw [D.laplacian_eq_sum_fderiv_of_harmonic (hf x) hharm.self_of_nhds]
  simp_rw [hsecond]
  have h := D.ricci_eq_principal_add_harmonicRicciQuadratic hharm u v
  linarith

end PoincareConjecture.LeviCivitaData
