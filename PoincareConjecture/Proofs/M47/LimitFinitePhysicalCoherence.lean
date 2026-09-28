import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCoherence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem limitFinite_physical_pullback_eq
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Q a : ℝ} {I J : Set ℝ} {U V : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin Q I U)
    (f : SurgeryFlowCylinder F C origin Q J V)
    (hU : IsOpen U) (hV : IsOpen V) (ha : a ≤ 0)
    (hI : Icc a 0 ⊆ I) (hJ : Icc a 0 ⊆ J)
    (hzero : ∀ x ∈ U ∩ V,
      e.forward 0 (hI ⟨ha, le_rfl⟩) x = f.forward 0 (hJ ⟨ha, le_rfl⟩) x)
    {x : C.carrier} (hx : x ∈ U ∩ V) (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner a (hI ⟨le_rfl, ha⟩) x v w =
      f.pullbackInner a (hJ ⟨le_rfl, ha⟩) x v w := by
  have heq : e.forward a (hI ⟨le_rfl, ha⟩) =ᶠ[𝓝 x]
      f.forward a (hJ ⟨le_rfl, ha⟩) := by
    filter_upwards [(hU.inter hV).mem_nhds hx] with y hy
    exact terminalCommonInterval_physical_eq e f ha hI hJ
      y hy.1 y hy.2 (hzero y hy)
  unfold SurgeryFlowCylinder.pullbackInner
  rw [heq.self_of_nhds, heq.mfderiv_eq]

end PoincareConjecture.M47
