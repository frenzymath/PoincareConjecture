import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Cylinder



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
  (hΩ : H.reference.regularLimitSet.Nonempty)
  {t : ℝ} (ht : t ∈ Ioo H.reference.tMinus T)
  (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04)
  (hR : (F.connection t).scalarCurvature N.center <
    (H.terminalConnection P04).scalarCurvature x₀)

include ht hR in
theorem regularNeckTerminalCylinder_old_parameter_mem {s : ℝ}
    (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hearly : T + s / (H.terminalConnection P04).scalarCurvature x₀ ≤ t) :
    (T + s / (H.terminalConnection P04).scalarCurvature x₀ - t) * N.scale⁻¹ ^ 2 ∈
      Ioc (-1 : ℝ) 0 := by
  rw [N.inverse_scale_sq_eq_scalar]
  exact (SingularRegularLimit.backward_clock_reparametrize ht.2 N.scalar_center_pos hR hs).2.1 hearly

theorem regularNeckTerminalCylinder_pointMap_old {s : ℝ}
    (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hearly : T + s / (H.terminalConnection P04).scalarCurvature x₀ ≤ t)
    (hr : (T + s / (H.terminalConnection P04).scalarCurvature x₀ - t) * N.scale⁻¹ ^ 2 ∈
      Ioc (-1 : ℝ) 0)
    (x : ((H.nonemptyExtension P04 hΩ).extended.slice T).carrier) :
    (H.regularNeckTerminalCylinder P04 hΩ ht N x₀ hR).pointMap s hs x =
      H.oldSpacetimeForward P04 (N.time_cylinder.pointMap
        ((T + s / (H.terminalConnection P04).scalarCurvature x₀ - t) * N.scale⁻¹ ^ 2) hr
        (H.terminalNeckToOld P04 ⟨ht.1.le, ht.2⟩ x)) := by
  rw [regularNeckTerminalCylinder, GeneralizedFlowCylinder.rebaseSource_pointMap]
  simp only [regularNeckSplicedCylinder, GeneralizedFlowCylinder.spliceBox,
    GeneralizedFlowCylinder.pointMap, GeneralizedFlowCylinder.spliceForward, dif_pos hearly]
  change (⟨T + s / (H.terminalConnection P04).scalarCurvature x₀,
    (H.regularNeckExtendedCylinder P04 hΩ ⟨ht.1.le, ht.2⟩ N x₀).forwardAtTime _ hr
      (H.terminalSliceHomeomorph P04 x)⟩ : H.extendedPoint P04) = _
  rw [GeneralizedFlowCylinder.forwardAtTime_point,
    H.regularNeckExtendedCylinder_pointMap P04 hΩ ⟨ht.1.le, ht.2⟩ N x₀]
  rfl

theorem regularNeckWeakenedTerminalCylinder_coordinate_pointMap_old
    {δ : ℝ} (hεδ : H.epsilon ≤ δ)
    (hcapture : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      N.carrier H.reference.regularLimitSet)
    {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hearly : T + s / (H.terminalConnection P04).scalarCurvature x₀ ≤ t)
    (hr : (T + s / (H.terminalConnection P04).scalarCurvature x₀ - t) * N.scale⁻¹ ^ 2 ∈
      Ioc (-1 : ℝ) 0)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-δ⁻¹) δ⁻¹) :
    (H.regularNeckWeakenedTerminalCylinder P04 hΩ ht N x₀ hR hεδ).pointMap s hs
        (H.terminalNeckCoordinateMap P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ) x₀ z) =
      H.oldSpacetimeForward P04 (N.time_cylinder.pointMap
        ((T + s / (H.terminalConnection P04).scalarCurvature x₀ - t) * N.scale⁻¹ ^ 2) hr
        (N.coordinate_map z)) := by
  change (H.regularNeckTerminalCylinder P04 hΩ ht N x₀ hR).pointMap s hs _ = _
  rw [H.regularNeckTerminalCylinder_pointMap_old P04 hΩ ht N x₀ hR hs hearly hr]
  rw [H.terminalNeckToOld_coordinateMap P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ) x₀
    (fun _ hy => hcapture (N.restrictAccuracy_carrier_subset hεδ hy)) z hz]
  rfl

end PoincareConjecture.SingularTimeAssumptions
