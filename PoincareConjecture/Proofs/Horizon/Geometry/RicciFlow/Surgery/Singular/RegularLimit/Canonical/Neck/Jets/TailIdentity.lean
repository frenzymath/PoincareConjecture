import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CenteredTensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.TailTensor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
  (hΩ : H.reference.regularLimitSet.Nonempty)
  {t : ℝ} (ht : t ∈ Ioo H.reference.tMinus T)
  (N : GeneralizedStrongNeck F t H.epsilon) (hε : H.epsilon < 1 / 2)
  (x₀ : H.regularRegion P04)
  (hR : (F.connection t).scalarCurvature N.center <
    (H.terminalConnection P04).scalarCurvature x₀)
  {δ : ℝ} (hεδ : H.epsilon ≤ δ)
  (hcapture : MapsTo (H.reference.inverse t ⟨ht.1.le, ht.2⟩)
    N.carrier H.reference.regularLimitSet)

include hcapture

theorem regularNeckWeakenedTerminalTensor_centered
    {s : ℝ} (hs : s ∈ Ioc (-1 : ℝ) 0)
    (hr : T + s / (H.terminalConnection P04).scalarCurvature x₀ ∈ Ioc H.reference.tMinus T)
    (z : RoundCylinderSpace) {p : E}
    (hp : cylinderHeightCovector p + z.2 ∈ Ioo (-δ⁻¹) δ⁻¹) :
    centeredCylinderMetric
        (H.regularNeckWeakenedTerminalTensor P04 hΩ ht N x₀ hR hεδ s) z.1 z.2 p =
      (H.terminalConnection P04).scalarCurvature x₀ •
        ((H.terminalFlow P04).metric
          (T + s / (H.terminalConnection P04).scalarCurvature x₀)).pullbackCoefficients
            (H.regularNeckCenteredLift P04 ⟨ht.1.le, ht.2⟩ N hε x₀ z) p := by
  rw [centeredCylinderMetric_congr
    (H.regularNeckWeakenedTerminalTensor_regular P04 hΩ ht N x₀ hR hεδ hcapture hs hr) _ _ hp,
    centeredCylinderMetric_smul,
    centeredCylinderMetric_pullback _
      (H.regularNeckSpatialMap_smooth P04 ⟨ht.1.le, ht.2⟩ N x₀ hcapture) _ _
      (DeepHorn.neckInterval_subset H.epsilon_pos hεδ hp),
    H.regularNeckSpatialMap_centered P04 ⟨ht.1.le, ht.2⟩ N hε x₀ z]

theorem regularNeckScaledOldTensor_centered (z : RoundCylinderSpace) {p : E}
    (hp : cylinderHeightCovector p + z.2 ∈ Ioo (-H.epsilon⁻¹) H.epsilon⁻¹) :
    centeredCylinderMetric (fun y v w =>
        ((H.terminalConnection P04).scalarCurvature x₀ /
          (F.connection t).scalarCurvature N.center) *
          generalizedCylinderPullback N.time_cylinder N.coordinate_map 0 y v w) z.1 z.2 p =
      (H.terminalConnection P04).scalarCurvature x₀ •
        ((H.terminalFlow P04).metric t).pullbackCoefficients
          (H.regularNeckCenteredLift P04 ⟨ht.1.le, ht.2⟩ N hε x₀ z) p := by
  have heq (y : RoundCylinderSpace) (hy : y.2 ∈ Ioo (-H.epsilon⁻¹) H.epsilon⁻¹)
      (v w : RoundCylinderTangent y) :
      ((H.terminalConnection P04).scalarCurvature x₀ /
        (F.connection t).scalarCurvature N.center) *
          generalizedCylinderPullback N.time_cylinder N.coordinate_map 0 y v w =
      (H.terminalConnection P04).scalarCurvature x₀ *
        roundCylinderPullback (F.metric t) N.coordinate_map y v w := by
    rw [N.pullback_zero hy, N.inverse_scale_sq_eq_scalar, ← mul_assoc,
      div_mul_cancel₀ _ N.scalar_center_pos.ne']
  rw [centeredCylinderMetric_congr heq _ _ hp, centeredCylinderMetric_smul,
    centeredCylinderMetric_pullback _ N.coordinate_map_smooth _ _ hp]
  congr 1
  exact (H.regularNeckCenteredLift_coefficients P04 ⟨ht.1.le, ht.2⟩ N hε x₀ hcapture z hp).symm

end PoincareConjecture.SingularTimeAssumptions
