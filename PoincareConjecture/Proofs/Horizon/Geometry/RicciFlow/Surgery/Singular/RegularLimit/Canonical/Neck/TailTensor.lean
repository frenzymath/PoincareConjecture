import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.RetainedComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Centered

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open Set Filter
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

def regularNeckSpatialMap {t ε : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    (N : GeneralizedStrongNeck F t ε) (x₀ : H.regularRegion P04) :
    RoundCylinderSpace → H.regularRegion P04 :=
  SingularRegularLimit.openRetraction (H.regularRegion P04) x₀ ∘
    (H.reference.inverse t ht ∘ N.coordinate_map)

theorem regularNeckSpatialMap_source {t ε : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    (N : GeneralizedStrongNeck F t ε) (x₀ : H.regularRegion P04)
    (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    H.regularNeckSourceMap P04 ht (H.regularNeckSpatialMap P04 ht N x₀ z) = N.coordinate_map z := by
  have hmem : N.coordinate_map z ∈ N.carrier :=
    N.coordinate_map_eq (z.1, ⟨z.2, hz⟩) ▸ (N.coordinate (z.1, ⟨z.2, hz⟩)).property
  change H.reference.forward t ht
    (SingularRegularLimit.openRetraction (H.regularRegion P04) x₀
      (H.reference.inverse t ht (N.coordinate_map z)) : M) = _
  rw [SingularRegularLimit.openRetraction_val _ _ (hcapture hmem), H.reference.right_inverse]

theorem regularNeckSpatialMap_smooth {t ε : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
    (N : GeneralizedStrongNeck F t ε) (x₀ : H.regularRegion P04)
    (hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (H.regularNeckSpatialMap P04 ht N x₀)
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) := by
  intro z hz
  rw [← ContMDiffWithinAt.subtypeVal_comp_iff (H.regularRegion P04)]
  apply (((H.reference.inverse_smooth t ht).comp_contMDiffOn N.coordinate_map_smooth) z hz).congr_of_mem
  · intro y hy
    exact SingularRegularLimit.openRetraction_val _ _ (hcapture
      (N.coordinate_map_eq (y.1, ⟨y.2, hy.2⟩) ▸ (N.coordinate (y.1, ⟨y.2, hy.2⟩)).property))
  · exact hz

theorem regularNeckSpatialMap_terminal_coordinate {t ε : ℝ}
    (ht : t ∈ Ico H.reference.tMinus T) (N : GeneralizedStrongNeck F t ε)
    (x₀ : H.regularRegion P04) (z : RoundCylinderSpace) :
    H.terminalSliceHomeomorph P04 (H.terminalNeckCoordinateMap P04 ht N x₀ z) =
      H.regularNeckSpatialMap P04 ht N x₀ z := by
  simp only [terminalNeckCoordinateMap, terminalNeckFromOld, Function.comp_apply,
    Homeomorph.apply_symm_apply]
  rfl

theorem regularNeckSpatialMap_centered {t ε : ℝ}
    (ht : t ∈ Ico H.reference.tMinus T) (N : GeneralizedStrongNeck F t ε)
    (hε : ε < 1 / 2) (x₀ : H.regularRegion P04) (z : RoundCylinderSpace) :
    H.regularNeckSpatialMap P04 ht N x₀ ∘ MetricSurgery.centeredCylinderLift z.1 z.2 =
      H.regularNeckCenteredLift P04 ht N hε x₀ z := rfl

variable (hΩ : H.reference.regularLimitSet.Nonempty)
  {t : ℝ} (ht : t ∈ Ioo H.reference.tMinus T)
  (N : GeneralizedStrongNeck F t H.epsilon) (x₀ : H.regularRegion P04)
  (hR : (F.connection t).scalarCurvature N.center <
    (H.terminalConnection P04).scalarCurvature x₀)
  {δ : ℝ} (hεδ : H.epsilon ≤ δ)
  (hcapture : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
    N.carrier H.reference.regularLimitSet)

include hcapture

theorem regularNeckWeakenedTerminalCylinder_pointMap_regular
    {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hr : T + s / (H.terminalConnection P04).scalarCurvature x₀ ∈ Ioc H.reference.tMinus T)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-δ⁻¹) δ⁻¹) :
    (H.regularNeckWeakenedTerminalCylinder P04 hΩ ht N x₀ hR hεδ).pointMap s hs
        (H.terminalNeckCoordinateMap P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ) x₀ z) =
      (⟨T + s / (H.terminalConnection P04).scalarCurvature x₀,
        (H.regularBox P04 hΩ).forward _ hr
          (H.regularNeckSpatialMap P04 ⟨ht.1.le, ht.2⟩ N x₀ z)⟩ : H.extendedPoint P04) := by
  change (H.regularNeckTerminalCylinder P04 hΩ ht N x₀ hR).pointMap s hs _ = _
  rw [regularNeckTerminalCylinder, GeneralizedFlowCylinder.rebaseSource_pointMap]
  change (H.regularNeckSplicedCylinder P04 hΩ ht N x₀ hR).pointMap s hs
    (H.terminalSliceHomeomorph P04 (H.terminalNeckCoordinateMap P04 ⟨ht.1.le, ht.2⟩
      (N.restrictAccuracy hεδ) x₀ z)) = _
  rw [H.regularNeckSpatialMap_terminal_coordinate]
  have hz' := DeepHorn.neckInterval_subset H.epsilon_pos hεδ hz
  have hx : H.regularNeckSourceMap P04 ⟨ht.1.le, ht.2⟩
      (H.regularNeckSpatialMap P04 ⟨ht.1.le, ht.2⟩ N x₀ z) ∈ N.carrier := by
    rw [H.regularNeckSpatialMap_source P04 ⟨ht.1.le, ht.2⟩ N x₀ hcapture z hz']
    exact N.coordinate_map_eq (z.1, ⟨z.2, hz'⟩) ▸ (N.coordinate (z.1, ⟨z.2, hz'⟩)).property
  simp only [regularNeckSplicedCylinder, GeneralizedFlowCylinder.spliceBox,
    GeneralizedFlowCylinder.pointMap, GeneralizedFlowCylinder.spliceForward]
  split_ifs with hcut
  · apply congrArg (Sigma.mk _)
    exact H.regularNeckExtendedCylinder_eq_regularBox P04 hΩ ⟨ht.1.le, ht.2⟩ N x₀
      ⟨hr.1, hcut.trans_lt ht.2⟩ _ _ hx
  · rfl

theorem regularNeckWeakenedTerminalTensor_regular
    {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hr : T + s / (H.terminalConnection P04).scalarCurvature x₀ ∈ Ioc H.reference.tMinus T)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-δ⁻¹) δ⁻¹)
    (v w : RoundCylinderTangent z) :
    H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR hεδ s z v w =
      (H.terminalConnection P04).scalarCurvature x₀ *
        roundCylinderPullback ((H.terminalFlow P04).metric
          (T + s / (H.terminalConnection P04).scalarCurvature x₀))
          (H.regularNeckSpatialMap P04 ⟨ht.1.le, ht.2⟩ N x₀) z v w := by
  let E := H.nonemptyExtension P04 hΩ
  let e := H.regularNeckWeakenedTerminalCylinder P04 hΩ ht N x₀ hR hεδ
  let f := H.terminalNeckCoordinateMap P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ) x₀
  let g := H.regularNeckSpatialMap P04 ⟨ht.1.le, ht.2⟩ N x₀
  let τ := T + s / (H.terminalConnection P04).scalarCurvature x₀
  have hcapture' : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      (N.restrictAccuracy hεδ).carrier H.reference.regularLimitSet :=
    fun _ hy => hcapture (N.restrictAccuracy_carrier_subset hεδ hy)
  have hf := H.terminalNeckCoordinateMap_smooth P04 ⟨ht.1.le, ht.2⟩
    (N.restrictAccuracy hεδ) x₀ hcapture'
  have hg := (H.regularNeckSpatialMap_smooth P04 ⟨ht.1.le, ht.2⟩ N x₀ hcapture).mono
    (prod_mono subset_rfl (DeepHorn.neckInterval_subset H.epsilon_pos hεδ))
  have hfmap : MapsTo f (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹)
      (H.terminalNeckCarrier P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ)) := by
    intro y hy
    change H.terminalNeckToOld P04 ⟨ht.1.le, ht.2⟩ (f y) ∈ (N.restrictAccuracy hεδ).carrier
    erw [H.terminalNeckToOld_coordinateMap P04 ⟨ht.1.le, ht.2⟩
      (N.restrictAccuracy hεδ) x₀ hcapture' y hy.2]
    exact (N.restrictAccuracy hεδ).coordinate_map_eq (y.1, ⟨y.2, hy.2⟩) ▸
      ((N.restrictAccuracy hεδ).coordinate (y.1, ⟨y.2, hy.2⟩)).property
  have hpoint (y : RoundCylinderSpace) (hy : y.2 ∈ Ioo (-δ⁻¹) δ⁻¹) :
      (⟨τ, (e.forward s hs ∘ f) y⟩ : E.extended.point) =
        ⟨τ, ((H.regularBox P04 hΩ).forward τ hr ∘ g) y⟩ :=
    H.regularNeckWeakenedTerminalCylinder_pointMap_regular P04 hΩ ht N x₀ hR hεδ hcapture hs hr y hy
  change generalizedCylinderPullback e f s z v w = _
  rw [e.tensor_eq_composite
    (H.terminalNeckCarrier_open P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ)) hf hfmap s hs z hz]
  rw [E.extended.roundCylinderPullback_of_point_eq rfl (e.forward s hs ∘ f)
    ((H.regularBox P04 hΩ).forward τ hr ∘ g) hpoint z hz]
  congr 1
  have hgz := (hg.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    (show z ∈ (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ : Set RoundCylinderSpace) from
      ⟨mem_univ _, hz⟩))).mdifferentiableAt (by simp)
  simp only [roundCylinderPullback, mfderiv_comp z
    (((H.regularBox P04 hΩ).forward_smooth τ hr (g z)).mdifferentiableAt (by simp)) hgz,
    ContinuousLinearMap.comp_apply, Function.comp_apply]
  exact (H.regularBox P04 hΩ).metric_pullback τ hr (g z) _ _

end PoincareConjecture.SingularTimeAssumptions
