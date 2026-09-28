import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64BoundedCoefficient_mul_integrable
    {a f : LoopPlane → ℝ} (ha : AEStronglyMeasurable a mu) (hf : Integrable f mu)
    {C : ℝ} (hb : ∀ p, |a p| ≤ C) : Integrable (fun p => a p * f p) mu :=
  hf.bdd_mul ha (Eventually.of_forall hb)

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

end PoincareConjecture
