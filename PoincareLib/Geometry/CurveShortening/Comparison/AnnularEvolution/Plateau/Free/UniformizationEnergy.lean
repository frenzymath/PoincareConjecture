import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.BoundaryModulus
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Weighted.AreaEnergy

/-!
# The energy identity required by free annular uniformization

Morrey's doubly-connected uniformization produces a positive cylinder modulus,
boundary lifts, and an a.e. conformal representative.  This file proves the
analytic part that is independent of that existence theorem: the weighted
Gram density of any such representative is exactly its actual annular area
density.  The uniformization existence and its epsilon approximation remain
outside this producer.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem m64_weighted_density_eq_area_of_conformal
    (g : RiemannianMetric n M) (f : LoopPlane → M)
    {r : ℝ} (hr : 0 < r) (z : LoopPlane)
    (hscale : r * m60AreaGram g f z 0 0 =
      r⁻¹ * m60AreaGram g f z 1 1)
    (horth : m60AreaGram g f z 0 1 = 0) :
    (r * m60AreaGram g f z 0 0 +
      r⁻¹ * m60AreaGram g f z 1 1) / 2 =
      m60AreaDensity g f z := by
  let a := m60AreaGram g f z 0 0
  let b := m60AreaGram g f z 1 1
  have ha : 0 ≤ a := m60AreaGram_diagonal_nonneg g f z 0
  have hb : 0 ≤ b := m60AreaGram_diagonal_nonneg g f z 1
  have hrne : r ≠ 0 := ne_of_gt hr
  have hscale' : b = r ^ 2 * a := by
    calc
      b = (r * r⁻¹) * b := by rw [mul_inv_cancel₀ hrne, one_mul]
      _ = r * (r⁻¹ * b) := by ring
      _ = r * (r * a) := by rw [← hscale]
      _ = r ^ 2 * a := by ring
  have hdet : Matrix.det (m60AreaGram g f z) = (r * a) ^ 2 := by
    rw [Matrix.det_fin_two, m60AreaGram_symm g f z 1 0, horth]
    simp only [zero_mul, sub_zero]
    change a * b = (r * a) ^ 2
    rw [hscale']
    ring
  have hnonneg : 0 ≤ r * a := mul_nonneg hr.le ha
  have harea : m60AreaDensity g f z = r * a := by
    unfold m60AreaDensity
    rw [hdet, max_eq_right (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hnonneg]
  rw [harea]
  rw [← hscale]
  ring

/-- A modulus-conformal free candidate has weighted energy equal to its actual annulus area.
This is the exact density/integral bridge needed after a genuine Morrey uniformization
construction supplies the candidate. Proof expansion for Morgan-Tian (2007), Lemma 19.15,
pp. 447-449. -/
theorem m64_weightedEnergy_eq_area_of_ae_modulus_conformal
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    m64ClassicalWeightedGramEnergy g A r = A.area := by
  unfold m64ClassicalWeightedGramEnergy M64Annulus.area m64AnnulusArea
  apply integral_congr_ae
  filter_upwards [hconf] with p hp
  exact m64_weighted_density_eq_area_of_conformal g A.map hr p hp.1 hp.2

/-- The original area-integrability field supplies integrability of the actual conformal
weighted density, with no boundary regularity premise. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449. -/
theorem m64_weightedGram_integrable_of_ae_modulus_conformal
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
      r⁻¹ * m60AreaGram g A.map p 1 1) / 2) m64AnnulusDomain volume := by
  apply A.area_integrable.congr
  filter_upwards [hconf] with p hp
  exact (m64_weighted_density_eq_area_of_conformal g A.map hr p hp.1 hp.2).symm

end PoincareMT
