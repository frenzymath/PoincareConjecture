import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum












set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem m60AreaDensity_le_weightedGram (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) {r : ℝ} (hr : 0 < r) :
    m60AreaDensity g f z ≤
      (r * m60AreaGram g f z 0 0 + r⁻¹ * m60AreaGram g f z 1 1) / 2 := by
  have h00 := m60AreaGram_diagonal_nonneg g f z 0
  have h11 := m60AreaGram_diagonal_nonneg g f z 1
  have hprod : (r * m60AreaGram g f z 0 0) * (r⁻¹ * m60AreaGram g f z 1 1) =
      m60AreaGram g f z 0 0 * m60AreaGram g f z 1 1 := by
    calc
      _ = (r * r⁻¹) * (m60AreaGram g f z 0 0 * m60AreaGram g f z 1 1) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hr.ne', one_mul]
  unfold m60AreaDensity
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [max_le_iff]
  refine ⟨sq_nonneg _, ?_⟩
  rw [Matrix.det_fin_two, m60AreaGram_symm g f z 1 0]
  nlinarith [sq_nonneg (r * m60AreaGram g f z 0 0 - r⁻¹ * m60AreaGram g f z 1 1),
    sq_nonneg (m60AreaGram g f z 0 1)]





theorem M64Annulus.area_le_weightedGramEnergy
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hE : IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
      r⁻¹ * m60AreaGram g A.map p 1 1) / 2) m64AnnulusDomain volume) :
    A.area ≤ ∫ p in m64AnnulusDomain,
      (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2 := by
  unfold M64Annulus.area m64AnnulusArea
  exact setIntegral_mono_on A.area_integrable hE m64AnnulusDomain_measurableSet
    (fun p _ => m60AreaDensity_le_weightedGram g A.map p hr)

end PoincareConjecture
