import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.HypersurfaceFields








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem inner_gradient_levelProjection (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hreg : 0 < D.levelQ f x)
    (v : TangentSpace (𝓡 n) x) :
    g.inner x (D.gradient f x) (D.levelProjection f x v) = 0 := by
  unfold levelProjection levelUnitNormal
  simp only [map_sub, map_smul, smul_apply, smul_eq_mul]
  change g.inner x (D.gradient f x) v -
    ((Real.sqrt (D.levelQ f x))⁻¹ * g.inner x (D.gradient f x) v) *
      ((Real.sqrt (D.levelQ f x))⁻¹ * D.levelQ f x) = 0
  have hs := Real.sq_sqrt hreg.le
  have hr := (Real.sqrt_pos.2 hreg).ne'
  field_simp
  rw [hs]
  ring



theorem levelMeanCurvature_eq_sum_inner_connection_normal (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hreg : 0 < D.levelQ f x) :
    D.levelMeanCurvature f x = ∑ i,
      g.inner x (D.connection (D.levelUnitNormal f) x
        (D.levelProjection f x (g.orthonormalBasis x i)))
        (D.levelProjection f x (g.orthonormalBasis x i)) := by
  unfold levelMeanCurvature levelSecondFundamental
  apply Finset.sum_congr rfl
  intro i _
  exact (D.inner_connection_unitNormal hf x hreg _ _
    (D.inner_gradient_levelProjection hreg _)).symm


noncomputable def levelVariation (D : LeviCivitaData g) (f h : M → ℝ) (x : M) : ℝ :=
  (g.inner x (D.gradient h x) (D.gradient f x) +
    h x * (D.laplacian f x -
      g.inner x (D.gradient (D.levelQ f) x) (D.gradient f x) / (2 * D.levelQ f x))) /
    D.levelQ f x

theorem levelVariation_eq_zero_of_notMem_tsupport (D : LeviCivitaData g)
    {f h : M → ℝ} {x : M} (hx : x ∉ tsupport h) : D.levelVariation f h x = 0 := by
  simp [levelVariation, D.gradient_eq_zero_of_notMem_tsupport hx,
    image_eq_zero_of_notMem_tsupport hx]

theorem tsupport_levelVariation_subset (D : LeviCivitaData g) (f h : M → ℝ) :
    tsupport (D.levelVariation f h) ⊆ tsupport h := by
  apply closure_minimal _ (isClosed_tsupport h)
  intro x hx
  by_contra hxh
  exact hx (D.levelVariation_eq_zero_of_notMem_tsupport hxh)

theorem hasCompactSupport_levelVariation (D : LeviCivitaData g)
    {f h : M → ℝ} (hc : HasCompactSupport h) :
    HasCompactSupport (D.levelVariation f h) :=
  hc.isCompact.of_isClosed_subset (isClosed_tsupport _) (D.tsupport_levelVariation_subset f h)

theorem contMDiff_levelVariation (D : LeviCivitaData g)
    {f h : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (hreg : ∀ x ∈ tsupport h, 0 < D.levelQ f x) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (D.levelVariation f h) := by
  intro x
  by_cases hx : x ∈ tsupport h
  · have hq := D.contMDiff_levelQ hf
    exact ((D.contMDiff_inner_gradient hh hf x).add ((hh x).mul
      ((D.contMDiff_laplacian hf x).sub
        ((D.contMDiff_inner_gradient hq hf x).div₀
          (contMDiffAt_const.mul (hq x)) (mul_ne_zero (by norm_num) (hreg x hx).ne'))))).div₀
      (hq x) (hreg x hx).ne'
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hx] with y hy
    exact D.levelVariation_eq_zero_of_notMem_tsupport hy



theorem levelVariation_eq_meanCurvature (D : LeviCivitaData g)
    {f h : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (hreg : 0 < D.levelQ f x) :
    D.levelVariation f h x =
      g.inner x (D.gradient h x) (D.gradient f x) / D.levelQ f x +
        h x * D.levelMeanCurvature f x / Real.sqrt (D.levelQ f x) := by
  rw [D.levelMeanCurvature_eq_scalarOperators hf x hreg]
  unfold levelVariation
  have hs := Real.sq_sqrt hreg.le
  have hr := (Real.sqrt_pos.2 hreg).ne'
  field_simp
  rw [hs]
  ring

end PoincareConjecture.LeviCivitaData
