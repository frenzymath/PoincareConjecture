import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

theorem forward_mfderiv_injective
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hU : IsOpen U) {s : ℝ} (hs : s ∈ I) {x : C.carrier} (hx : x ∈ U) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x) := by
  have hf := ((e.forward_smooth s hs x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hinv := (e.inverse_smooth s hs (e.forward s hs x) ⟨x, hx, rfl⟩).mdifferentiableWithinAt
    (by simp)
  have hu : UniqueMDiffWithinAt (𝓡 3) U x := hU.uniqueMDiffWithinAt hx
  have hcomp := mfderivWithin_comp x hinv hf.mdifferentiableWithinAt
    (fun y hy => ⟨y, hy, rfl⟩) hu
  have hleft : ∀ y ∈ U, (e.inverse s hs ∘ e.forward s hs) y = id y :=
    e.left_inverse s hs
  rw [mfderivWithin_congr_of_mem hleft hx, mfderivWithin_id hu,
    mfderivWithin_eq_mfderiv hu hf] at hcomp
  intro v w hvw
  have h := congrArg
    (mfderivWithin (𝓡 3) (𝓡 3) (e.inverse s hs) (e.forward s hs '' U) (e.forward s hs x)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hcomp] at h
  exact h

end PoincareConjecture.GeneralizedFlowCylinder
