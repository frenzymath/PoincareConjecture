import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CylinderTensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Coordinates.Worldlines
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ModelComparison



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
  {δ : ℝ} (hεδ : H.epsilon ≤ δ)

def regularNeckWeakenedTerminalTensor : ℝ → RoundCylinderTwoTensor :=
  generalizedCylinderPullback
    (H.regularNeckWeakenedTerminalCylinder P04 hΩ ht N x₀ hR hεδ)
    (H.terminalNeckCoordinateMap P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ) x₀)

theorem regularNeckWeakenedTerminalTensor_old
    (hcapture : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      N.carrier H.reference.regularLimitSet)
    {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hearly : T + s / (H.terminalConnection P04).scalarCurvature x₀ ≤ t)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-δ⁻¹) δ⁻¹)
    (v w : RoundCylinderTangent z) :
    H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR hεδ s z v w =
      ((H.terminalConnection P04).scalarCurvature x₀ / (N.scale⁻¹ ^ 2)) *
        generalizedCylinderPullback N.time_cylinder N.coordinate_map
          ((T + s / (H.terminalConnection P04).scalarCurvature x₀ - t) * N.scale⁻¹ ^ 2)
          z v w := by
  let E := H.nonemptyExtension P04 hΩ
  let d := E.pushCylinder N.time_cylinder ⟨N.center⟩
  let e := H.regularNeckWeakenedTerminalCylinder P04 hΩ ht N x₀ hR hεδ
  let f := H.terminalNeckCoordinateMap P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ) x₀
  have hcapture' : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      (N.restrictAccuracy hεδ).carrier H.reference.regularLimitSet :=
    fun _ hy => hcapture (N.restrictAccuracy_carrier_subset hεδ hy)
  have hfmap : MapsTo f (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹)
      (H.terminalNeckCarrier P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ)) := by
    intro y hy
    change H.terminalNeckCoordinateMap P04 ⟨ht.1.le, ht.2⟩
      (N.restrictAccuracy hεδ) x₀ y ∈ _
    erw [← H.terminalNeckCoordinateMap_eq P04 ⟨ht.1.le, ht.2⟩
      (N.restrictAccuracy hεδ) x₀ hcapture' (y.1, ⟨y.2, hy.2⟩)]
    exact (H.terminalNeckCoordinate P04 ⟨ht.1.le, ht.2⟩
      (N.restrictAccuracy hεδ) x₀ hcapture' _).property
  have hgmap : MapsTo N.coordinate_map (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹) N.carrier := by
    intro y hy
    have hy' := DeepHorn.neckInterval_subset H.epsilon_pos hεδ hy.2
    exact N.coordinate_map_eq (y.1, ⟨y.2, hy'⟩) ▸ (N.coordinate (y.1, ⟨y.2, hy'⟩)).property
  have hr := H.regularNeckTerminalCylinder_old_parameter_mem P04 ht N x₀ hR hs hearly
  have hpoint (y : RoundCylinderSpace) (hy : y.2 ∈ Ioo (-δ⁻¹) δ⁻¹) :
      e.pointMap s hs (f y) =
        d.pointMap ((T + s / (H.terminalConnection P04).scalarCurvature x₀ - t) *
          N.scale⁻¹ ^ 2) hr (N.coordinate_map y) := by
    rw [E.pushCylinder_pointMap]
    exact H.regularNeckWeakenedTerminalCylinder_coordinate_pointMap_old
      P04 hΩ ht N x₀ hR hεδ hcapture hs hearly hr y hy
  have hmetric := e.tensor_eq_of_pointMap_eq d
    (H.terminalNeckCarrier_open P04 ⟨ht.1.le, ht.2⟩ (N.restrictAccuracy hεδ)) N.carrier_open
    (H.terminalNeckCoordinateMap_smooth P04 ⟨ht.1.le, ht.2⟩
      (N.restrictAccuracy hεδ) x₀ hcapture')
    (N.restrictAccuracy hεδ).coordinate_map_smooth hfmap hgmap hs hr
    (N.time_cylinder.physical_clock_eq _).symm hpoint z hz v w
  change generalizedCylinderPullback e f s z v w = _
  rw [hmetric]
  congr 1
  simp only [generalizedCylinderPullback, dif_pos hr]
  exact E.pushCylinder_pullbackInner N.time_cylinder ⟨N.center⟩ N.carrier_open
    _ hr _ (hgmap ⟨mem_univ _, hz⟩) _ _



theorem regularNeckWeakenedTerminalTensor_retained_comparison
    (hcapture : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
      N.carrier H.reference.regularLimitSet)
    (hc : 1 ≤ (H.terminalConnection P04).scalarCurvature x₀ /
      (F.connection t).scalarCurvature N.center)
    (hcmax : (H.terminalConnection P04).scalarCurvature x₀ /
      (F.connection t).scalarCurvature N.center ≤ 6 / 5)
    (hcε : (H.terminalConnection P04).scalarCurvature x₀ /
      (F.connection t).scalarCurvature N.center - 1 ≤ H.epsilon / 4)
    (hdε : (H.terminalConnection P04).scalarCurvature x₀ * (T - t) ≤ H.epsilon / 4) :
    RoundCylinderFamilyClose (2 * H.epsilon)
      (Ioc (-1 : ℝ) 0 ∩ Iic (-((H.terminalConnection P04).scalarCurvature x₀ * (T - t))))
      (H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR
        (show H.epsilon ≤ 2 * H.epsilon by linarith [H.epsilon_pos])) := by
  let Q := (H.terminalConnection P04).scalarCurvature x₀
  let q := (F.connection t).scalarCurvature N.center
  have hq : 0 < q := N.scalar_center_pos
  have hQ : 0 < Q := N.scalar_center_pos.trans hR
  have hbase := SingularRegularLimit.roundCylinderFamilyClose_retained_clock
    H.epsilon_pos hc hcmax hcε
    (mul_nonneg hQ.le (sub_nonneg.mpr ht.2.le)) hdε N.metric_comparison
  apply RoundCylinderFamilyClose.congr (B' := fun s z v w =>
    (Q / q) * generalizedCylinderPullback N.time_cylinder N.coordinate_map
      ((Q * (T - t) + s) / (Q / q)) z v w) _ hbase
  intro s hs z hz v w
  have hearly : T + s / Q ≤ t := by
    have hcut : s ≤ -(Q * (T - t)) := hs.2
    have hdiv : s / Q ≤ t - T := (div_le_iff₀ hQ).2 (by nlinarith)
    linarith
  rw [H.regularNeckWeakenedTerminalTensor_old P04 hΩ ht N x₀ hR _ hcapture hs.1 hearly z hz]
  apply congrArg₂ (fun a b : ℝ => a * b)
  · exact congrArg (fun a => Q / a) N.inverse_scale_sq_eq_scalar
  · apply congrArg (fun r => generalizedCylinderPullback N.time_cylinder N.coordinate_map r z v w)
    rw [N.inverse_scale_sq_eq_scalar]
    change (T + s / Q - t) * q = (Q * (T - t) + s) / (Q / q)
    field_simp
    ring

end PoincareConjecture.SingularTimeAssumptions
