import PoincareConjecture.Proofs.M10.SupportedCalculus
import Mathlib.Topology.OpenPartialHomeomorph.Basic









set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M10

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


noncomputable def chartSupportedTest (e : OpenPartialHomeomorph M E) (φ : M → ℝ) : E → ℝ :=
  e.target.indicator (φ ∘ e.symm)

omit [NormedSpace ℝ E] in

theorem chartSupportedTest_eventuallyEq (e : OpenPartialHomeomorph M E) (φ : M → ℝ)
    {x : E} (hx : x ∈ e.target) :
    chartSupportedTest e φ =ᶠ[𝓝 x] φ ∘ e.symm :=
  eqOn_indicator.eventuallyEq_of_mem (e.open_target.mem_nhds hx)

omit [NormedSpace ℝ E] in

theorem chartSupportedTest_support (e : OpenPartialHomeomorph M E) {φ : M → ℝ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source) :
    HasCompactSupport (chartSupportedTest e φ) ∧
      tsupport (chartSupportedTest e φ) ⊆ e '' tsupport φ ∧
      tsupport (chartSupportedTest e φ) ⊆ e.target := by
  classical
  have hK : IsCompact (e '' tsupport φ) :=
    hc.image_of_continuousOn (e.continuousOn.mono hs)
  have hsub : tsupport (chartSupportedTest e φ) ⊆ e '' tsupport φ := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    have hxt : x ∈ e.target := by
      by_contra hnot
      exact hx (indicator_of_notMem hnot _)
    have hφ : φ (e.symm x) ≠ 0 := by
      simpa only [Function.mem_support, chartSupportedTest, indicator_of_mem hxt,
        Function.comp_apply] using hx
    exact ⟨e.symm x, subset_tsupport φ hφ, e.right_inv hxt⟩
  exact ⟨hK.of_isClosed_subset (isClosed_tsupport _) hsub, hsub,
    hsub.trans (image_subset_iff.mpr (fun q hq ↦ e.map_source (hs hq)))⟩


theorem chartSupportedTest_contDiff (e : OpenPartialHomeomorph M E) {φ : M → ℝ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ e.source) {k : ℕ∞ω}
    (hf : ContDiffOn ℝ k (φ ∘ e.symm) e.target) :
    ContDiff ℝ k (chartSupportedTest e φ) := by
  apply contDiff_of_contDiffOn_of_tsupport_subset e.open_target _
    (chartSupportedTest_support e hc hs).2.2
  intro x hx
  exact ((hf.contDiffAt (e.open_target.mem_nhds hx)).congr_of_eventuallyEq
    (chartSupportedTest_eventuallyEq e φ hx)).contDiffWithinAt

end PoincareConjecture.M10
