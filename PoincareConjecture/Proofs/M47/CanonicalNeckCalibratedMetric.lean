import PoincareConjecture.Proofs.M47.CanonicalNeckCoarseMetric
import PoincareConjecture.Proofs.M47.CanonicalNeckClosedScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open M36 M44 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem negativeCylinder_coefficient_calibrated_bounds {epsilon t : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (ht : t ∈ Icc (-1 : ℝ) 0) {B : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon t B) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (v : E) :
    (41 / 50 : ℝ) * ‖v‖ ^ 2 ≤ centeredCylinderMetric B z.1 z.2 0 v v ∧
      centeredCylinderMetric B z.1 z.2 0 v v ≤ (209 / 50 : ℝ) * ‖v‖ ^ 2 := by
  have hsplit := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v v)
    cylinderHorizontalForm_add_vertical
  change cylinderHorizontalForm v v + cylinderHeightCovector v * cylinderHeightCovector v =
    inner ℝ v v at hsplit
  rw [real_inner_self_eq_norm_sq] at hsplit
  have hH : 0 ≤ cylinderHorizontalForm v v := by
    rw [cylinderHorizontalForm_apply]
    exact real_inner_self_nonneg
  have hmodel : ‖v‖ ^ 2 ≤ evolvingCylinderModelField t 0 v v ∧
      evolvingCylinderModelField t 0 v v ≤ 4 * ‖v‖ ^ 2 := by
    rw [evolvingCylinderModelField_zero]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    have htime : 2 * (1 - t) ≤ 4 := by linarith [ht.1]
    constructor
    · nlinarith [ht.2]
    · nlinarith [mul_le_mul_of_nonneg_right htime hH,
        sq_nonneg (cylinderHeightCovector v)]
  have herr : |centeredCylinderMetric B z.1 z.2 0 v v -
      evolvingCylinderModelField t 0 v v| ≤ 36 * epsilon * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖centeredCylinderMetric B z.1 z.2 0 - evolvingCylinderModelField t 0‖ *
          ‖v‖ * ‖v‖ :=
        (centeredCylinderMetric B z.1 z.2 0 - evolvingCylinderModelField t 0).le_opNorm₂ v v
      _ ≤ (36 * epsilon) * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (negativeCylinder_coefficient_error hepsilon ht hB z hz) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  have herror : 36 * epsilon * ‖v‖ ^ 2 ≤ (9 / 50 : ℝ) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖v‖)
  constructor <;> linarith [(abs_le.mp herr).1, (abs_le.mp herr).2, hmodel.1, hmodel.2]

theorem neck_metric_le_calibrated
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0) (hsmall : N.epsilon ≤ 1 / 200)
    (g : RiemannianMetric 3 M) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 0)
    (hclose : RoundCylinderClose N.epsilon t
      (fun z v w => (N.scale⁻¹ ^ 2) * roundCylinderPullback g N.coordinate_map z v w))
    (x : M) (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    g.inner x v v ≤ (23 / 10 : ℝ) ^ 2 * g0.inner x v v := by
  let Q := N.scale⁻¹ ^ 2
  have hQ : 0 < Q := pow_pos (inv_pos.mpr N.scale_pos) 2
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  let f := centeredNeckLift N z.1 z.2
  have hzero : (0 : E) ∈ centeredNeckDomain N z.2 := zero_mem_centeredNeckDomain N hz
  have hcoeff := scaled_neck_pullback_coefficients N g hQ z.1 z.2 hzero
  have hcoeff0 := scaled_neck_pullback_coefficients N g0 hQ z.1 z.2 hzero
  have hold : RoundCylinderClose N.epsilon 0
      (fun z v w => Q * roundCylinderPullback g0 N.coordinate_map z v w) :=
    N.metric_comparison.close
  have hlocal (w : E) :
      g.inner (f 0) (mfderiv (𝓡 3) (𝓡 3) f 0 w) (mfderiv (𝓡 3) (𝓡 3) f 0 w) ≤
        (23 / 10 : ℝ) ^ 2 * g0.inner (f 0) (mfderiv (𝓡 3) (𝓡 3) f 0 w)
          (mfderiv (𝓡 3) (𝓡 3) f 0 w) := by
    have hu := (negativeCylinder_coefficient_calibrated_bounds
      N.epsilon_pos hsmall ht hclose z hz w).2
    have hl := (negativeCylinder_coefficient_calibrated_bounds N.epsilon_pos hsmall
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num) hold z hz w).1
    rw [← hcoeff] at hu
    rw [← hcoeff0] at hl
    change Q * g.inner (f 0) (mfderiv (𝓡 3) (𝓡 3) f 0 w)
      (mfderiv (𝓡 3) (𝓡 3) f 0 w) ≤ (209 / 50 : ℝ) * ‖w‖ ^ 2 at hu
    change (41 / 50 : ℝ) * ‖w‖ ^ 2 ≤ Q * g0.inner (f 0)
      (mfderiv (𝓡 3) (𝓡 3) f 0 w) (mfderiv (𝓡 3) (𝓡 3) f 0 w) at hl
    apply (mul_le_mul_iff_right₀ hQ).mp
    nlinarith only [hu, hl, sq_nonneg ‖w‖]
  have hfzero : f 0 = x := by
    rw [show f 0 = N.coordinate_map (z.1, z.2) from centeredNeckLift_zero N z.1 z.2]
    exact neck_coordinate_inverse N hx
  obtain ⟨e, he⟩ := centeredNeckLift_mfderiv_isInvertible N z.1 z.2 hzero
  have hsur : Function.Surjective (mfderiv (𝓡 3) (𝓡 3) f 0) := by
    rw [← he]
    exact e.surjective
  obtain ⟨w, hw⟩ := hsur v
  calc
    g.inner x v v = g.inner (f 0) v v :=
      (congrArg (fun y : M => g.inner y v v) hfzero).symm
    _ ≤ (23 / 10 : ℝ) ^ 2 * g0.inner (f 0) v v := by simpa only [hw] using hlocal w
    _ = (23 / 10 : ℝ) ^ 2 * g0.inner x v v :=
      congrArg (fun y : M => (23 / 10 : ℝ) ^ 2 * g0.inner y v v) hfzero

theorem ordinary_closed_neck_metric_le_calibrated
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {J : Set ℝ} (G : RicciFlow 3 M J) (T : ℝ)
    (N : EpsilonNeck (G.metric T)) (hsmall : N.epsilon ≤ 1 / 200)
    (hclock : ∀ s ∈ Icc (-1 : ℝ) 0, T + s / (N.scale⁻¹ ^ 2) ∈ J)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => (N.scale⁻¹ ^ 2) * roundCylinderPullback
        (G.metric (T + s / (N.scale⁻¹ ^ 2))) N.coordinate_map z v w))
    (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : M) (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    (G.metric (T + s / (N.scale⁻¹ ^ 2))).inner x v v ≤
      (23 / 10 : ℝ) ^ 2 * (G.metric T).inner x v v := by
  have hstrict (a : ℝ) (ha : a ∈ Ioc (-1 : ℝ) 0) :
      (G.metric (T + a / (N.scale⁻¹ ^ 2))).inner x v v ≤
        (23 / 10 : ℝ) ^ 2 * (G.metric T).inner x v v :=
    neck_metric_le_calibrated N hsmall _ ⟨ha.1.le, ha.2⟩ (hfamily.at_time ha) x hx v
  have hmetric : ContinuousOn (fun t : ℝ => (G.metric t).inner x v v) J :=
    fun t ht => (G.equation t ht x v v).continuousWithinAt
  have hcont : ContinuousOn
      (fun a : ℝ => (G.metric (T + a / (N.scale⁻¹ ^ 2))).inner x v v)
      (Icc (-1 : ℝ) 0) := hmetric.comp (by fun_prop) hclock
  have hclosure : closure (Ioc (-1 : ℝ) 0) = Icc (-1 : ℝ) 0 :=
    closure_Ioc (by norm_num)
  exact le_on_closure hstrict (hclosure.symm ▸ hcont) continuousOn_const
    (hclosure.symm ▸ hs)

end PoincareConjecture.Proofs.M47
