import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.LevelCutoff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def levelQ (D : LeviCivitaData g) (f : M → ℝ) (x : M) : ℝ :=
  g.inner x (D.gradient f x) (D.gradient f x)

def levelUnitNormal (D : LeviCivitaData g) (f : M → ℝ) (x : M) :
    TangentSpace (𝓡 n) x :=
  (Real.sqrt (D.levelQ f x))⁻¹ • D.gradient f x

def levelProjection (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (v : TangentSpace (𝓡 n) x) : TangentSpace (𝓡 n) x :=
  v - (g.inner x (D.levelUnitNormal f x) v) • D.levelUnitNormal f x

def levelSecondFundamental (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (v w : TangentSpace (𝓡 n) x) : ℝ :=
  D.hessian f x (D.levelProjection f x v) (D.levelProjection f x w) /
    Real.sqrt (D.levelQ f x)

def levelMeanCurvature (D : LeviCivitaData g) (f : M → ℝ) (x : M) : ℝ :=
  ∑ i, D.levelSecondFundamental f x (g.orthonormalBasis x i) (g.orthonormalBasis x i)

def levelGaussTerm (D : LeviCivitaData g) (f : M → ℝ) (x : M) : ℝ :=
  (D.levelMeanCurvature f x) ^ 2 -
    ∑ i, ∑ j, (D.levelSecondFundamental f x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2

def levelBochnerDifference (D : LeviCivitaData g) (f : M → ℝ) (x : M) : ℝ :=
  D.levelGaussTerm f x -
    D.ricci x (D.levelUnitNormal f x) (D.levelUnitNormal f x)

theorem contMDiff_levelQ (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (D.levelQ f) :=
  D.contMDiff_inner_gradient hf hf

theorem levelGaussTerm_eq_scalarOperators (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hreg : 0 < D.levelQ f x) :
    D.levelGaussTerm f x =
      ((D.laplacian f x) ^ 2 -
        (∑ i, ∑ j, (D.hessian f x
          (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2)) / D.levelQ f x -
        D.laplacian f x * g.inner x (D.gradient (D.levelQ f) x) (D.gradient f x) /
          (D.levelQ f x) ^ 2 +
        g.inner x (D.gradient (D.levelQ f) x) (D.gradient (D.levelQ f) x) /
          (2 * (D.levelQ f x) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := D.connection (D.gradient f) x
  have hA (v w : TangentSpace (𝓡 n) x) : inner ℝ (A v) w = inner ℝ v (A w) := by
    change g.inner x (A v) w = g.inner x v (A w)
    rw [g.symm x v]
    exact (D.hessian_eq_inner_connection_gradient (hf x) v w).symm.trans
      ((D.hessian_symm hf x v w).trans (D.hessian_eq_inner_connection_gradient (hf x) w v))
  let q := D.levelQ f
  let r := Real.sqrt (q x)
  let v := D.gradient f x
  let u := r⁻¹ • v
  have hr : 0 < r := Real.sqrt_pos.2 hreg
  have hrq : r ^ 2 = q x := Real.sq_sqrt hreg.le
  have hu : inner ℝ u u = 1 := by
    change g.inner x (r⁻¹ • v) (r⁻¹ • v) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    change r⁻¹ * (r⁻¹ * q x) = 1
    rw [← hrq]
    field_simp
  have hgrad : D.gradient q x = (2 : ℝ) • A v := by
    apply (g.inner_isInvertible x).injective
    ext w
    rw [D.inner_gradient]
    change mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x w = _
    rw [D.mvfderiv_gradient_normSq (hf x), D.hessian_symm hf x w,
      D.hessian_eq_inner_connection_gradient (hf x)]
    simp only [map_smul, smul_apply, smul_eq_mul, A, v]
  have hgauss := Poincare.LinearAlgebra.gauss_term_orthogonal_restriction
    (g.orthonormalBasis x) A hA u hu
  have hinner (v w : TangentSpace (𝓡 n) x) : inner ℝ v w = g.inner x v w := rfl
  simp only [hinner, A] at hgauss
  change
    (∑ i, D.hessian f x
      (g.orthonormalBasis x i - (g.inner x u (g.orthonormalBasis x i)) • u)
      (g.orthonormalBasis x i - (g.inner x u (g.orthonormalBasis x i)) • u) / r) ^ 2 -
      (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i - (g.inner x u (g.orthonormalBasis x i)) • u)
        (g.orthonormalBasis x j - (g.inner x u (g.orthonormalBasis x j)) • u) / r) ^ 2) =
    ((D.laplacian f x) ^ 2 -
      (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2)) / q x -
      D.laplacian f x * g.inner x (D.gradient q x) v / (q x) ^ 2 +
      g.inner x (D.gradient q x) (D.gradient q x) / (2 * (q x) ^ 2)
  simp_rw [div_pow, ← Finset.sum_div]
  rw [div_pow, ← sub_div]
  simp_rw [D.hessian_eq_inner_connection_gradient (hf x)]
  rw [hgauss]
  have hlap : D.laplacian f x = ∑ i, inner ℝ (A (g.orthonormalBasis x i))
      (g.orthonormalBasis x i) := D.laplacian_eq_sum_inner_connection_gradient (hf x)
  simp only [hinner, A] at hlap
  rw [hlap, hgrad]
  simp only [u, map_smul, smul_apply, smul_eq_mul, A]
  rw [← hrq]
  field_simp

theorem levelMeanCurvature_eq_scalarOperators (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hreg : 0 < D.levelQ f x) :
    D.levelMeanCurvature f x =
      (D.laplacian f x -
        g.inner x (D.gradient (D.levelQ f) x) (D.gradient f x) /
          (2 * D.levelQ f x)) / Real.sqrt (D.levelQ f x) := by
  have hmean := D.hessian_mean_curvature hf x hreg
  change D.levelMeanCurvature f x =
    (D.laplacian f x - D.hessian f x
      (D.levelUnitNormal f x) (D.levelUnitNormal f x)) /
      Real.sqrt (D.levelQ f x) at hmean
  rw [hmean]
  congr 2
  have hcross : g.inner x (D.gradient (D.levelQ f) x) (D.gradient f x) =
      2 * D.hessian f x (D.gradient f x) (D.gradient f x) := by
    rw [D.inner_gradient]
    exact D.mvfderiv_gradient_normSq (hf x) _
  rw [hcross]
  simp_rw [levelUnitNormal, D.hessian_eq_inner_connection_gradient (hf x)]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hs := Real.sq_sqrt hreg.le
  have hr := (Real.sqrt_pos.2 hreg).ne'
  field_simp [hreg.ne']
  rw [hs]
  ring

theorem levelBochnerDifference_eq_scalarOperators (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hreg : 0 < D.levelQ f x) :
    D.levelBochnerDifference f x =
      ((D.laplacian f x) ^ 2 +
        g.inner x (D.gradient (D.laplacian f) x) (D.gradient f x) -
        (1 / 2 : ℝ) * D.laplacian (D.levelQ f) x) / D.levelQ f x -
        D.laplacian f x * g.inner x (D.gradient (D.levelQ f) x) (D.gradient f x) /
          (D.levelQ f x) ^ 2 +
        g.inner x (D.gradient (D.levelQ f) x) (D.gradient (D.levelQ f) x) /
          (2 * (D.levelQ f x) ^ 2) := by
  have hricci (c : ℝ) (v : TangentSpace (𝓡 n) x) :
      D.ricci x (c • v) (c • v) = c ^ 2 * D.ricci x v v := by
    unfold ricci
    simp_rw [← D.curvatureTensor_bilinear_first_third_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring
  unfold levelBochnerDifference
  rw [D.levelGaussTerm_eq_scalarOperators hf x hreg, levelUnitNormal, hricci]
  rw [inv_pow, Real.sq_sqrt hreg.le]
  have hb := D.bochner_identity hf x
  change D.laplacian (D.levelQ f) x = _ at hb
  rw [← D.inner_gradient] at hb
  rw [hb]
  ring

theorem continuousOn_levelMeanCurvature (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn (D.levelMeanCurvature f) {x | 0 < D.levelQ f x} := by
  have hq := D.contMDiff_levelQ hf
  have hden : ∀ x ∈ {x | 0 < D.levelQ f x}, 2 * D.levelQ f x ≠ 0 :=
    fun x hx => mul_ne_zero (by norm_num) hx.ne'
  have hsqrt : ∀ x ∈ {x | 0 < D.levelQ f x}, Real.sqrt (D.levelQ f x) ≠ 0 :=
    fun x hx => (Real.sqrt_pos.2 hx).ne'
  apply ContinuousOn.congr
    (((D.continuous_laplacian hf).continuousOn.sub
      ((D.continuous_inner_gradient hq hf).continuousOn.div
        (continuous_const.mul hq.continuous).continuousOn hden)).div
          hq.continuous.sqrt.continuousOn hsqrt)
  intro x hx
  exact D.levelMeanCurvature_eq_scalarOperators hf x hx

theorem continuousOn_levelBochnerDifference (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn (D.levelBochnerDifference f) {x | 0 < D.levelQ f x} := by
  have hq := D.contMDiff_levelQ hf
  have hlap := D.contMDiff_laplacian hf
  have hden : ∀ x ∈ {x | 0 < D.levelQ f x}, D.levelQ f x ≠ 0 :=
    fun x hx => hx.ne'
  have hden2 : ∀ x ∈ {x | 0 < D.levelQ f x}, (D.levelQ f x) ^ 2 ≠ 0 :=
    fun x hx => pow_ne_zero _ (hden x hx)
  have hden3 : ∀ x ∈ {x | 0 < D.levelQ f x}, 2 * (D.levelQ f x) ^ 2 ≠ 0 :=
    fun x hx => mul_ne_zero (by norm_num) (hden2 x hx)
  have hc₁ : Continuous (fun x => (D.laplacian f x) ^ 2 +
      g.inner x (D.gradient (D.laplacian f) x) (D.gradient f x) -
      (1 / 2 : ℝ) * D.laplacian (D.levelQ f) x) :=
    ((hlap.continuous.pow 2).add (D.continuous_inner_gradient hlap hf)).sub
      (continuous_const.mul (D.continuous_laplacian hq))
  have hc₂ := hlap.continuous.mul (D.continuous_inner_gradient hq hf)
  have hc₃ := D.continuous_inner_gradient hq hq
  refine ContinuousOn.congr
    (((hc₁.continuousOn.div hq.continuous.continuousOn hden).sub
      (hc₂.continuousOn.div (hq.continuous.pow 2).continuousOn hden2)).add
      (hc₃.continuousOn.div
        (continuous_const.mul (hq.continuous.pow 2)).continuousOn hden3)) ?_
  intro x hx
  exact D.levelBochnerDifference_eq_scalarOperators hf x hx

end PoincareConjecture.LeviCivitaData
