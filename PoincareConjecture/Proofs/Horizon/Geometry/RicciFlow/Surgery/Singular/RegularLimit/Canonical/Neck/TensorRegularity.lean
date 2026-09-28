import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.RoundCylinderCongruence



set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale ε : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder F C origin scale I U)
  {coordinate : RoundCylinderSpace → C.carrier}



theorem pullback_tensor_smooth (hU : IsOpen U)
    (hcoordinate : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hmap : MapsTo coordinate (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) U)
    (s : ℝ) (hs : s ∈ I) :
    RoundCylinderTensorSmoothOn ε (generalizedCylinderPullback e coordinate s) := by
  have hcomp := (e.forward_smooth s hs).comp hcoordinate hmap
  apply (roundCylinderTensorSmoothOn_smul_pullback
    (F.metric (origin + s / scale)) hcomp scale).congr
  intro z hz v w
  have hzc : z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ := ⟨mem_univ _, hz⟩
  have hd := ((e.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (hmap hzc))).mdifferentiableAt (by simp)
  have hc := (hcoordinate.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hzc)).mdifferentiableAt (by simp)
  simp only [generalizedCylinderPullback, dif_pos hs, pullbackInner,
    roundCylinderPullback, mfderiv_comp z hd hc, ContinuousLinearMap.comp_apply,
    Function.comp_apply]

end PoincareConjecture.GeneralizedFlowCylinder
