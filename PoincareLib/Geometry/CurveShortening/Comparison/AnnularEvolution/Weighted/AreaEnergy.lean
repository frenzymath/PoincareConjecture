import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Infimum

/-!
# Annular area is bounded by Dirichlet energy at every positive modulus

Reciprocal weights preserve the product of the diagonal Gram entries.
The weighted arithmetic-geometric mean inequality therefore controls
the actual Jacobian, including at degenerate points.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- At every positive modulus the actual area density is bounded by the weighted Gram
half-trace, including degenerate differentials. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
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

/-- The actual annular area is bounded by every integrable positive-modulus Gram energy.
Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
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

end PoincareMT
