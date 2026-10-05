import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AreaEnergy.Comparison.Density
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The regularized areas converge to the actual sphere area

Morgan-Tian Lemma 18.10, printed pp. 424-426, with the area-to-energy
erratum. The regularization uses the actual pullback metric, and dominated
convergence retains genuine integrability of all the sphere densities.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Actual regularized sphere areas approach the original area, without
any immersion hypothesis. Source: MT Lemma 18.10, pp. 424-426, erratum. -/
theorem m60SphereRegularizedMetric_area_tendsto (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) :
    Tendsto (fun k : ℕ => m60SphereArea
      (m60SphereRegularizedMetric g f hf ((k : ℝ) + 1)⁻¹ (by positivity)) id)
      atTop (𝓝 (m60SphereArea g f)) := by
  let q (k : ℕ) := m60SphereRegularizedMetric g f hf ((k : ℝ) + 1)⁻¹ (by positivity)
  have hd : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hpoint (z : LoopPlane) :
      Tendsto (fun k : ℕ => m60SphereAreaDensity (q k) id z)
        atTop (𝓝 (m60SphereAreaDensity g f z)) := by
    simp only [m60SphereAreaDensity, m60AreaDensity, Function.id_comp,
      q, m60SphereRegularizedMetric_det]
    have hc : Tendsto (fun _ : ℕ => Matrix.det (m60AreaGram g (f ∘ m60SphereParameter) z))
        atTop (𝓝 (Matrix.det (m60AreaGram g (f ∘ m60SphereParameter) z))) :=
      tendsto_const_nhds
    have hdet := (hc.add
      (((hd.const_mul 2).mul_const (16 / (‖z‖ ^ 2 + 4) ^ 2)).mul_const
        (m60SphereEnergyDensity g f z))).add
      ((hd.pow 2).mul_const ((16 / (‖z‖ ^ 2 + 4) ^ 2) ^ 2))
    simpa only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] using
      ((show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds).max hdet).sqrt
  change Tendsto (fun k : ℕ => ∫ z : LoopPlane, m60SphereAreaDensity (q k) id z)
    atTop (𝓝 (∫ z : LoopPlane, m60SphereAreaDensity g f z))
  refine tendsto_integral_of_dominated_convergence
    (fun z => m60SphereEnergyDensity g f z + 16 / (‖z‖ ^ 2 + 4) ^ 2) ?_ ?_ ?_ ?_
  · intro k
    exact (m60SphereAreaDensity_integrable (q k) id contMDiff_id).aestronglyMeasurable
  · exact (m60SphereEnergyDensity_integrable g f (hf.of_le (by simp))).add
      m60SphereParameter_factor_integrable
  · intro k
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (show 0 ≤ m60SphereAreaDensity (q k) id z from
      m60AreaDensity_nonneg (q k) (id ∘ m60SphereParameter) z)]
    apply m60SphereRegularizedMetric_areaDensity_bound
    exact inv_le_one_of_one_le₀ (by have h := Nat.cast_nonneg (α := ℝ) k; linarith)
  · exact Filter.Eventually.of_forall hpoint

/-- A positive regularization has area within any prescribed positive
error of the original map. Source: MT Lemma 18.10, pp. 424-426, erratum. -/
theorem m60SphereRegularizedMetric_exists_area_lt (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ (delta : ℝ) (hdelta : 0 < delta),
      m60SphereArea (m60SphereRegularizedMetric g f hf delta hdelta) id <
        m60SphereArea g f + eta := by
  have hevent := (m60SphereRegularizedMetric_area_tendsto g f hf).eventually
    (gt_mem_nhds (show m60SphereArea g f < m60SphereArea g f + eta by linarith))
  obtain ⟨k, hk⟩ := hevent.exists
  exact ⟨((k : ℝ) + 1)⁻¹, by positivity, hk⟩

end PoincareMT
