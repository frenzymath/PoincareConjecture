import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature








set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

private theorem sqrt_mul_inverse_scalar_scale {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    Real.sqrt c * R ^ (-1 / 2 : ℝ) = (c⁻¹ * R) ^ (-1 / 2 : ℝ) := by
  rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hR.le, Real.inv_rpow hc.le,
    neg_div, Real.rpow_neg hc.le, inv_inv, Real.sqrt_eq_rpow]



theorem roundCylinderPullback_normalized_rescaledMetric
    (g : RiemannianMetric 3 M) (c : ℝ) (hc : 0 < c)
    (s : ℝ) (coordinate : RoundCylinderSpace → M) :
    (fun z v w => (Real.sqrt c * s)⁻¹ ^ 2 *
      roundCylinderPullback (rescaledMetric g c hc) coordinate z v w) =
      (fun z v w => s⁻¹ ^ 2 * roundCylinderPullback g coordinate z v w) := by
  funext z v w
  simp only [roundCylinderPullback, rescaledMetric_inner, mul_inv_rev, mul_pow]
  field_simp
  rw [Real.sq_sqrt hc.le]


noncomputable def EpsilonNeck.rescale
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (c : ℝ) (hc : 0 < c) :
    EpsilonNeck (rescaledMetric g c hc) where
  epsilon := N.epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := N.epsilon_lt_half
  scale := Real.sqrt c * N.scale
  scale_pos := mul_pos (Real.sqrt_pos.mpr hc) N.scale_pos
  center := N.center
  connection := rescaledMetric_connection g N.connection c hc
  scalar_center_pos := by
    rw [rescaledMetric_scalarCurvature]
    exact mul_pos (inv_pos.mpr hc) N.scalar_center_pos
  scale_eq_scalar := by
    rw [rescaledMetric_scalarCurvature, N.scale_eq_scalar]
    exact sqrt_mul_inverse_scalar_scale hc N.scalar_center_pos
  carrier := N.carrier
  carrier_open := N.carrier_open
  coordinate := N.coordinate
  coordinate_map := N.coordinate_map
  coordinate_map_eq := N.coordinate_map_eq
  coordinate_map_smooth := N.coordinate_map_smooth
  coordinate_inverse := N.coordinate_inverse
  coordinate_inverse_mem := N.coordinate_inverse_mem
  coordinate_inverse_left := N.coordinate_inverse_left
  coordinate_inverse_right := N.coordinate_inverse_right
  coordinate_inverse_smooth := N.coordinate_inverse_smooth
  central_sphere := N.central_sphere
  central_sphere_eq := N.central_sphere_eq
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := N.central_sphere_subset
  metric_comparison := ⟨by
    rw [roundCylinderPullback_normalized_rescaledMetric]
    exact N.metric_comparison.close⟩

@[simp] theorem EpsilonNeck.rescale_scale
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (c : ℝ) (hc : 0 < c) :
    (N.rescale c hc).scale = Real.sqrt c * N.scale := rfl

@[simp] theorem EpsilonNeck.rescale_coordinate
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (c : ℝ) (hc : 0 < c) :
    (N.rescale c hc).coordinate = N.coordinate := rfl

@[simp] theorem EpsilonNeck.rescale_region
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (c : ℝ) (hc : 0 < c)
    (a b : ℝ) :
    (N.rescale c hc).region a b = N.region a b := rfl

theorem EpsilonNeck.exists_rescaledMetric
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (c : ℝ) (hc : 0 < c) :
    ∃ N' : EpsilonNeck (rescaledMetric g c hc),
      N'.epsilon = N.epsilon ∧
      N'.scale = Real.sqrt c * N.scale ∧
      N'.center = N.center ∧
      N'.connection = rescaledMetric_connection g N.connection c hc ∧
      N'.carrier = N.carrier ∧
      N'.coordinate_map = N.coordinate_map ∧
      N'.coordinate_inverse = N.coordinate_inverse ∧
      N'.central_sphere = N.central_sphere := by
  exact ⟨N.rescale c hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem EpsilonNeck.exists_of_metric_eq
    {g g' : RiemannianMetric 3 M} (h : g = g') (N : EpsilonNeck g) :
    ∃ N' : EpsilonNeck g',
      N'.epsilon = N.epsilon ∧
      N'.scale = N.scale ∧
      N'.center = N.center ∧
      N'.carrier = N.carrier ∧
      N'.coordinate_map = N.coordinate_map ∧
      N'.coordinate_inverse = N.coordinate_inverse ∧
      N'.central_sphere = N.central_sphere := by
  subst g'
  exact ⟨N, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem EpsilonNeck.exists_of_rescaledMetric
    {g : RiemannianMetric 3 M} (c : ℝ) (hc : 0 < c)
    (N : EpsilonNeck (rescaledMetric g c hc)) :
    ∃ N' : EpsilonNeck g,
      N'.epsilon = N.epsilon ∧
      N'.scale = N.scale / Real.sqrt c ∧
      N'.center = N.center ∧
      N'.carrier = N.carrier ∧
      N'.coordinate_map = N.coordinate_map ∧
      N'.coordinate_inverse = N.coordinate_inverse ∧
      N'.central_sphere = N.central_sphere := by
  have hmetric : rescaledMetric (rescaledMetric g c hc) c⁻¹ (inv_pos.mpr hc) = g := by
    cases g
    simp only [rescaledMetric, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  obtain ⟨N', heps, hscale, hcenter, hcarrier, hcoord, hinv, hsphere⟩ :=
    EpsilonNeck.exists_of_metric_eq hmetric (N.rescale c⁻¹ (inv_pos.mpr hc))
  refine ⟨N', heps, ?_, hcenter, hcarrier, hcoord, hinv, hsphere⟩
  rw [hscale]
  change Real.sqrt c⁻¹ * N.scale = N.scale / Real.sqrt c
  rw [Real.sqrt_inv, div_eq_mul_inv, mul_comm]

end PoincareConjecture
