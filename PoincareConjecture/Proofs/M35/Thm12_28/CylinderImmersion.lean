import PoincareConjecture.Definitions.Ch11.BlowupLimits
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.GeneralizedFlowCylinder

theorem mfderiv_injective {F : GeneralizedRicciFlowData}
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C a Q I U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ I) {z : C.carrier} (hz : z ∈ U) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) z) := by
  have hu := hU.uniqueMDiffOn (I := 𝓡 3) z hz
  have hf := ((e.forward_smooth s hs).contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt
    (by simp)
  have hg := (e.inverse_smooth s hs) (e.forward s hs z) ⟨z, hz, rfl⟩
  have hd := mfderivWithin_comp z
    (hg.mdifferentiableWithinAt (by simp))
    (hf.mdifferentiableWithinAt (s := U))
    (fun y hy => ⟨y, hy, rfl⟩) hu
  have hc : mfderivWithin (𝓡 3) (𝓡 3) (e.inverse s hs ∘ e.forward s hs) U z =
      mfderivWithin (𝓡 3) (𝓡 3) id U z :=
    mfderivWithin_congr_of_mem (fun y hy => e.left_inverse s hs hy) hz
  rw [hc, mfderivWithin_id hu, mfderivWithin_eq_mfderiv hu hf] at hd
  apply Function.LeftInverse.injective
    (g := mfderivWithin (𝓡 3) (𝓡 3) (e.inverse s hs) (e.forward s hs '' U)
      (e.forward s hs z))
  intro v
  exact (congrArg (fun L => L v) hd).symm

end PoincareConjecture.GeneralizedFlowCylinder
