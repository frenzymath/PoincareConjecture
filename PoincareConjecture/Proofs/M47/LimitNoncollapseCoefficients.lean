import PoincareConjecture.Proofs.M47.LimitRP2Charts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}


noncomputable def limitNoncollapseChartForm
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (q : C.carrier) (t : ℝ) (ht : t ∈ I) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  scale • (F.metric (origin + t / scale)).pullbackCoefficients
    (e.forward t ht ∘ (extChartAt (𝓡 3) q).symm) z



theorem limitNoncollapseChartForm_apply
    (e : GeneralizedFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (q : C.carrier) (t : ℝ) (ht : t ∈ I) (z : EuclideanSpace ℝ (Fin 3))
    (hz : z ∈ (extChartAt (𝓡 3) q).target)
    (hzu : (extChartAt (𝓡 3) q).symm z ∈ U)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    limitNoncollapseChartForm e q t ht z v w =
      e.pullbackInner t ht ((extChartAt (𝓡 3) q).symm z)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z v)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z w) := by
  have he := ((e.forward_smooth t ht).mdifferentiableOn (by simp) _ hzu).mdifferentiableAt
    (hU.mem_nhds hzu)
  have hc := ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hz)).mdifferentiableAt (by simp)
  change scale * (F.metric _).inner _
      (mfderiv (𝓡 3) (𝓡 3) (e.forward t ht ∘ (extChartAt (𝓡 3) q).symm) z v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward t ht ∘ (extChartAt (𝓡 3) q).symm) z w) = _
  rw [mfderiv_comp z he hc]
  rfl



theorem limitNoncollapseChartForm_coefficient {J : Set ℝ} {L : BlowupLimitFlow.{u} J}
    {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder F L.sliceCarrier origin scale I U) (hU : IsOpen U)
    (q : L.sliceCarrier.carrier) (t : ℝ) (ht : t ∈ I)
    (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ (extChartAt (𝓡 3) q).target)
    (hzu : (extChartAt (𝓡 3) q).symm z ∈ U) (a b : Fin 3) :
    limitNoncollapseChartForm e q t ht z (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b) = blowupPullbackCoefficient e q a b (t, z) := by
  rw [limitNoncollapseChartForm_apply e hU q t ht z hz hzu]
  simp only [blowupPullbackCoefficient, dif_pos ht]

end PoincareConjecture.M47
