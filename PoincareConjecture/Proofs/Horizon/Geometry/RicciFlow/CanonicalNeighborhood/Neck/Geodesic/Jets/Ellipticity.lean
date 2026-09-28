import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Model

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

local instance centeredEllipticityProductCharts :
    ChartedSpace RoundCylinderCoordinates RoundCylinderSpace :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere ℝ ℝ

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem normalized_pullback_lower
    (N : EpsilonNeck g) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderTangent z) :
    (1 - N.epsilon) * EvolvingRoundCylinderMetric 0 z v v ≤
      N.normalized_pullback z v v := by
  have h := N.pullback_metric_bounds hz v
  have hscale : 0 ≤ N.scale⁻¹ ^ 2 := sq_nonneg _
  calc
    (1 - N.epsilon) * EvolvingRoundCylinderMetric 0 z v v =
        N.scale⁻¹ ^ 2 * ((1 - N.epsilon) * N.scale ^ 2 *
          EvolvingRoundCylinderMetric 0 z v v) := by
      field_simp [N.scale_pos.ne']
    _ ≤ N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v :=
      mul_le_mul_of_nonneg_left h.1 hscale
    _ = N.normalized_pullback z v v := rfl

theorem normalized_pullback_upper
    (N : EpsilonNeck g) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderTangent z) :
    N.normalized_pullback z v v ≤
      (1 + N.epsilon) * EvolvingRoundCylinderMetric 0 z v v := by
  have h := N.pullback_metric_bounds hz v
  have hscale : 0 ≤ N.scale⁻¹ ^ 2 := sq_nonneg _
  calc
    N.normalized_pullback z v v =
        N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v v := rfl
    _ ≤ N.scale⁻¹ ^ 2 * ((1 + N.epsilon) * N.scale ^ 2 *
          EvolvingRoundCylinderMetric 0 z v v) :=
      mul_le_mul_of_nonneg_left h.2 hscale
    _ = (1 + N.epsilon) * EvolvingRoundCylinderMetric 0 z v v := by
      field_simp [N.scale_pos.ne']

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem centered_coefficients_eq_pullback
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderCoordinates) :
    N.normalizedCenteredCoefficients q (0, s) v w =
      N.normalized_pullback (q, s)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1, v.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 w.1, w.2) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let T : RoundCylinderCoordinates →L[ℝ] RoundCylinderTangent (q, s) :=
    ((mfderiv (𝓡 2) (𝓡 2) c.symm 0).comp
      (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)
  let P := (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    N.coordinate_map (q, s)).comp T
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (N.coordinate_map (q, s))) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (N.coordinate_map (q, s))) := by
    unfold TangentSpace
    infer_instance
  let B := N.scale⁻¹ ^ 2 • (g.inner (N.coordinate_map (q, s))).bilinearComp P P
  have hb (i j : Fin 3) :
      N.normalizedCenteredCoefficients q (0, s)
          (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) =
        B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) := by
    have h := (N.normalizedCenteredCoefficients_basis_eventuallyEq q
      (y := (0, s)) hs i j).self_of_nhds
    have h' := h.symm
    dsimp only [roundCylinderTensorCoefficient] at h'
    erw [sphere_chart_symm_zero] at h'
    exact h'
  change N.normalizedCenteredCoefficients q (0, s) v w = B v w
  rw [cylinderCoordinate_decomposition v, cylinderCoordinate_decomposition w]
  simp only [map_add, map_smul, add_apply, smul_apply, hb]

theorem normalizedCenteredCoefficients_lower
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderCoordinates) :
    (1 - N.epsilon) * ‖v‖ ^ 2 ≤
      N.normalizedCenteredCoefficients q (0, s) v v := by
  rw [centered_coefficients_eq_pullback N q hs v v]
  let u : RoundCylinderTangent (q, s) :=
    (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1, v.2)
  have h := N.normalized_pullback_lower (z := (q, s)) hs u
  have hmodel : ‖v‖ ^ 2 ≤ EvolvingRoundCylinderMetric 0 (q, s) u u := by
    have hinner := roundSphereMetric_chart_symm_inner q 0 v.1 v.1
    rw [sphere_chart_symm_zero] at hinner
    change ‖v‖ ^ 2 ≤ 2 * (1 - 0) * (roundSphereMetric 2).inner q
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1)
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1) + v.2 * v.2
    erw [hinner]
    simpa only [roundCylinderModelCoefficients_apply, sub_zero, mul_one, mul_assoc] using
      (roundCylinderModelCoefficients_center_quadratic_bounds s v).1
  exact (mul_le_mul_of_nonneg_left hmodel
    (by linarith [N.epsilon_lt_half])).trans h

end PoincareConjecture.EpsilonNeck
