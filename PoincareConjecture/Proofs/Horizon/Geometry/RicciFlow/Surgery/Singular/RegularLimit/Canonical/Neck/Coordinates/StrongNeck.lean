import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Center
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.RetainedComparison



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture

namespace SingularRegularLimit

private def cylinderWithScale {F : GeneralizedRicciFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin q q' : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (h : q = q') (e : GeneralizedFlowCylinder F C origin q I U) :
    GeneralizedFlowCylinder F C origin q' I U := h ▸ e

private theorem cylinderWithScale_pointMap {F : GeneralizedRicciFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin q q' : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (h : q = q') (e : GeneralizedFlowCylinder F C origin q I U)
    (s : ℝ) (hs : s ∈ I) (x : C.carrier) :
    (cylinderWithScale h e).pointMap s hs x = e.pointMap s hs x := by
  subst q'
  rfl

private theorem cylinderWithScale_pullback {F : GeneralizedRicciFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin q q' : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (h : q = q') (e : GeneralizedFlowCylinder F C origin q I U)
    (f : RoundCylinderSpace → C.carrier) :
    generalizedCylinderPullback (cylinderWithScale h e) f = generalizedCylinderPullback e f := by
  subst q'
  rfl

end SingularRegularLimit

namespace SingularTimeAssumptions

open SingularRegularLimit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
  (hΩ : H.reference.regularLimitSet.Nonempty)
  {t : ℝ} (ht : t ∈ Ioo H.reference.tMinus T)
  (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04)
  (hcenter : N.center = H.reference.forward t ⟨ht.1.le, ht.2⟩ x₀)
  (hR : (F.connection t).scalarCurvature N.center <
    (H.terminalConnection P04).scalarCurvature x₀)
  {δ : ℝ} (hεδ : H.epsilon ≤ δ)
  (hcapture : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
    N.carrier H.reference.regularLimitSet)
  (hclose : RoundCylinderFamilyClose δ (Ioc (-1 : ℝ) 0)
    (H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR hεδ))



def terminalStrongNeckOfComparison : GeneralizedStrongNeck (H.nonemptyExtension P04 hΩ).extended T δ := by
  let Q := (H.terminalConnection P04).scalarCurvature x₀
  let W := N.restrictAccuracy hεδ
  have hQ : 0 < Q := N.scalar_center_pos.trans hR
  have hcapture' : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      W.carrier H.reference.regularLimitSet :=
    fun _ hy => hcapture (N.restrictAccuracy_carrier_subset hεδ hy)
  have hscalar : ((H.nonemptyExtension P04 hΩ).extended.connection T).scalarCurvature
      ((H.terminalSliceHomeomorph P04).symm x₀) = Q := by
    change (H.extendedSliceGeometry P04 T).connection.scalarCurvature _ = Q
    rw [← H.terminalSliceHomeomorph_scalar_pullback P04, Homeomorph.apply_symm_apply]
  have hscale : (Q ^ (-1 / 2 : ℝ))⁻¹ ^ 2 = Q := by
    rw [neg_div, Real.rpow_neg hQ.le, ← Real.sqrt_eq_rpow, inv_inv, Real.sq_sqrt hQ.le]
  exact {
    epsilon_pos := H.epsilon_pos.trans_le hεδ
    center := (H.terminalSliceHomeomorph P04).symm x₀
    scalar_center_pos := hscalar.symm ▸ hQ
    scale := Q ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hQ _
    scale_scalar := by rw [hscalar]
    carrier := H.terminalNeckCarrier P04 ⟨ht.1.le, ht.2⟩ W
    carrier_open := H.terminalNeckCarrier_open P04 ⟨ht.1.le, ht.2⟩ W
    coordinate := H.terminalNeckCoordinate P04 ⟨ht.1.le, ht.2⟩ W x₀ hcapture'
    coordinate_map := H.terminalNeckCoordinateMap P04 ⟨ht.1.le, ht.2⟩ W x₀
    coordinate_map_eq := H.terminalNeckCoordinateMap_eq P04 ⟨ht.1.le, ht.2⟩ W x₀ hcapture'
    coordinate_map_smooth := H.terminalNeckCoordinateMap_smooth P04 ⟨ht.1.le, ht.2⟩ W x₀ hcapture'
    coordinate_inverse := H.terminalNeckCoordinateInverse P04 ⟨ht.1.le, ht.2⟩ W
    coordinate_inverse_mem := H.terminalNeckCoordinateInverse_mem P04 ⟨ht.1.le, ht.2⟩ W
    coordinate_inverse_left := H.terminalNeckCoordinateInverse_left P04 ⟨ht.1.le, ht.2⟩ W x₀ hcapture'
    coordinate_inverse_right := H.terminalNeckCoordinateInverse_right P04 ⟨ht.1.le, ht.2⟩ W x₀
    coordinate_inverse_smooth := H.terminalNeckCoordinateInverse_smooth P04 ⟨ht.1.le, ht.2⟩ W
    central_sphere := H.terminalNeckCentralSphere P04 ⟨ht.1.le, ht.2⟩ W x₀
    central_sphere_eq := H.terminalNeckCentralSphere_eq P04 ⟨ht.1.le, ht.2⟩ W x₀
    center_on_central_sphere := H.terminalNeckCenter_on_centralSphere P04 ⟨ht.1.le, ht.2⟩ W x₀ hcenter
    central_sphere_subset := H.terminalNeckCentralSphere_subset P04 ⟨ht.1.le, ht.2⟩ W x₀ hcapture'
    time_cylinder := cylinderWithScale hscale.symm
      (H.regularNeckWeakenedTerminalCylinder P04 hΩ ht N x₀ hR hεδ)
    cylinder_identity := by
      intro h x _
      rw [cylinderWithScale_pointMap]
      exact H.regularNeckWeakenedTerminalCylinder_identity P04 hΩ ht N x₀ hR hεδ h x
    metric_comparison := by
      rw [cylinderWithScale_pullback]
      exact hclose }

theorem terminalStrongNeckOfComparison_center :
    (H.terminalStrongNeckOfComparison P04 hΩ ht N x₀ hcenter hR hεδ hcapture hclose).center =
      (H.terminalSliceHomeomorph P04).symm x₀ := rfl

end SingularTimeAssumptions
end PoincareConjecture
