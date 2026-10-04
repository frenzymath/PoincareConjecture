import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.TriangularEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Integral convergence for the actual bounded source coefficients against an L1 field.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

/-- A measurable bounded source coefficient multiplies an actual L1 field integrably.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. -/
theorem m64BoundedCoefficient_mul_integrable
    {a f : LoopPlane → ℝ} (ha : AEStronglyMeasurable a mu) (hf : Integrable f mu)
    {C : ℝ} (hb : ∀ p, |a p| ≤ C) : Integrable (fun p => a p * f p) mu :=
  hf.bdd_mul ha (Eventually.of_forall hb)

/-- One eventual coefficient bound and pointwise convergence give convergence of the actual
weighted integrals. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary
analysis. -/
theorem m64BoundedCoefficient_integral_tendsto
    {a : ℝ → LoopPlane → ℝ} {a0 f : LoopPlane → ℝ}
    (ha : ∀ t, AEStronglyMeasurable (a t) mu) (hf : Integrable f mu)
    {C : ℝ} (hb : ∀ᶠ t : ℝ in 𝓝 0, ∀ p, |a t p| ≤ C)
    (hl : ∀ p, Tendsto (fun t => a t p) (𝓝 0) (𝓝 (a0 p))) :
    Tendsto (fun t => ∫ p in S, a t p * f p) (𝓝 0) (𝓝 (∫ p in S, a0 p * f p)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun p => C * |f p|)
    (Eventually.of_forall fun t => (ha t).mul hf.aestronglyMeasurable)
  · filter_upwards [hb] with t ht
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul_of_nonneg_right (ht p) (abs_nonneg _)
  · exact hf.norm.const_mul C
  · exact Eventually.of_forall fun p => (hl p).mul_const (f p)

end PoincareMT
