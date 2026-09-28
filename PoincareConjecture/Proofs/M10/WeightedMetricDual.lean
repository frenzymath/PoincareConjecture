import PoincareConjecture.Proofs.M10.MetricDualDerivative
import PoincareConjecture.Proofs.M10.SupportedCalculus

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def weightedMetricDual (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (ρ f : E → ℝ) (x : E) : E :=
  ρ x • (B x).inverse (fderiv ℝ f x)

theorem weightedMetricDual_contDiffAt
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ f : E → ℝ} {x : E}
    (hB : ContDiffAt ℝ 1 B x) (hρ : ContDiffAt ℝ 1 ρ x)
    (hf : ContDiffAt ℝ 2 f x) (hi : (B x).IsInvertible) :
    ContDiffAt ℝ 1 (weightedMetricDual B ρ f) x :=
  hρ.smul (metricDual_contDiffAt hB hf hi)

omit [CompleteSpace E] in

theorem tsupport_weightedMetricDual_subset
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (ρ f : E → ℝ) :
    tsupport (weightedMetricDual B ρ f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hnot
  apply hx
  simp only [weightedMetricDual, fderiv_of_notMem_tsupport ℝ hnot, map_zero, smul_zero]

theorem weightedMetricDual_contDiff_of_tsupport_subset
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {ρ f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hρ : ContDiffOn ℝ 1 ρ U)
    (hf : ContDiffOn ℝ 2 f U) (hi : ∀ x ∈ U, (B x).IsInvertible)
    (hs : tsupport f ⊆ U) :
    ContDiff ℝ 1 (weightedMetricDual B ρ f) := by
  apply contDiff_of_contDiffOn_of_tsupport_subset hU _
    ((tsupport_weightedMetricDual_subset B ρ f).trans hs)
  intro x hx
  exact (weightedMetricDual_contDiffAt (hB.contDiffAt (hU.mem_nhds hx))
    (hρ.contDiffAt (hU.mem_nhds hx)) (hf.contDiffAt (hU.mem_nhds hx))
    (hi x hx)).contDiffWithinAt

omit [CompleteSpace E] in

theorem weightedMetricDual_hasCompactSupport
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (ρ : E → ℝ) {f : E → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (weightedMetricDual B ρ f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_weightedMetricDual_subset B ρ f)

end PoincareConjecture.M10
