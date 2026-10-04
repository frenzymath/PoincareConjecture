import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

/-!
# Extending within smoothness by a supported scalar factor

A smooth cutoff supported in an open set extends local within smoothness
to the entire parameter set. This is the partition step for actual field
realization in Morgan-Tian Proposition 6.37, pp. 123-127.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.M14

/-- A globally smooth scalar supported inside the local domain makes
a locally within-smooth vector function smooth on the full set,
as used in the partition step of Proposition 6.37, pp. 123-127. -/
theorem contDiffOn_smul_of_tsupport_subset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {C U : Set E} (hU : IsOpen U) {ρ : E → ℝ} {f : E → F}
    (hρ : ContDiff ℝ ∞ ρ) (hf : ContDiffOn ℝ ∞ f (C ∩ U))
    (hsupport : tsupport ρ ⊆ U) : ContDiffOn ℝ ∞ (fun x => ρ x • f x) C := by
  intro x hx
  by_cases hs : x ∈ tsupport ρ
  · apply (hρ.contDiffAt.contDiffWithinAt.smul (hf x ⟨hx, hsupport hs⟩)).mono_of_mem_nhdsWithin
    exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds (hsupport hs)))
  · have heq : (fun x => ρ x • f x) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hs] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact contDiffWithinAt_const.congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

end PoincareMT.M14
