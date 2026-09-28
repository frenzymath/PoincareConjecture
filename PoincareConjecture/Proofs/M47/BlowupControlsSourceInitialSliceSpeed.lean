import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSliceChart
import PoincareConjecture.Proofs.M47.BlowupControlsCapModelEnergy
import PoincareConjecture.Proofs.M47.BlowupControlsCapMetricError
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderMetricComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M36 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
  {origin scale : ℝ} {I : Set ℝ}
  (e : SurgeryFlowCylinder F C origin scale I N.carrier)


theorem source_neck_slice_native_lower
    (hsmall : N.epsilon ≤ 1 / 2) (s : ℝ) (hs : s ∈ I) (hs0 : s ≤ 0)
    (hclose : RoundCylinderClose N.epsilon s (surgeryCylinderPullback e N.coordinate_map s))
    (q : UnitTwoSphere) {c : ℝ} (hc : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : E) :
    let p := M35.cylinderCoordinateEquiv.symm (0, c)
    let f := e.forward s hs ∘ centeredNeckLift N q 0
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ scale * (F.metric (origin + s / scale)).inner
      (f p) (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p v) := by
  let p := M35.cylinderCoordinateEquiv.symm ((0, c) : RoundCylinderCoordinates)
  have hp : p ∈ centeredNeckDomain N 0 := by
    change (M35.cylinderCoordinateEquiv p).2 + 0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply, add_zero] using hc
  obtain ⟨g1, D1, W, hW, hpW, hcoeff, _hscalar⟩ :=
    source_neck_slice_metric_realization N e s hs q hc
  have htime : s < 1 := hs0.trans_lt (by norm_num)
  let g0 := M35.cylinderEuclideanMetric s htime
  let D0 := D1.withMetric g0
  have hnorm := cap_model_derivative_norm_le N.epsilon_pos htime
    (surgeryCylinderPullback e N.coordinate_map s) hclose g1 D0 q hW hcoeff c hc hpW
    0 (Nat.zero_le _)
  have hquad := cap_metricDifference_quadratic_le g0 g1 p v
  have hg0 : 0 ≤ g0.inner p v v := by
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact (g0.pos p v hv).le
  have herror : |g1.inner p v v - g0.inner p v v| ≤ N.epsilon * g0.inner p v v :=
    hquad.trans (mul_le_mul_of_nonneg_right hnorm hg0)
  have hmodel : ‖v‖ ^ 2 ≤ g0.inner p v v :=
    M35.cylinderEuclideanCoefficients_lower hs0 c v
  have hmetric : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g1.inner p v v := by
    have hsmall' := mul_le_mul_of_nonneg_right hsmall hg0
    linarith only [(abs_le.mp herror).1, hsmall', hmodel]
  rw [source_neck_slice_metric_of_coefficients N e s hs q g1 hp (hcoeff p hpW) v v] at hmetric
  exact hmetric



theorem source_neck_slice_axial_derivative
    (hsmall : N.epsilon ≤ 1 / 2) (s : ℝ) (hs : s ∈ I) (hs0 : s ≤ 0)
    (hclose : RoundCylinderClose N.epsilon s (surgeryCylinderPullback e N.coordinate_map s))
    {x : (F.slice (origin + s / scale)).carrier}
    (hx : x ∈ e.forward s hs '' N.carrier) (w : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse (e.inverse s hs y)).2) x w| ≤
      (2 * Real.sqrt scale) * (F.metric (origin + s / scale)).tangentNorm x w := by
  obtain ⟨y, hy, rfl⟩ := hx
  let z := N.coordinate_inverse y
  let p := M35.cylinderCoordinateEquiv.symm ((0, z.2) : RoundCylinderCoordinates)
  let f := e.forward s hs ∘ centeredNeckLift N z.1 0
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (N.coordinate_inverse_mem y hy).2
  have hp : p ∈ centeredNeckDomain N 0 := by
    change (M35.cylinderCoordinateEquiv p).2 + 0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply, add_zero] using hz
  have hpoint : f p = e.forward s hs y := by
    dsimp only [f, Function.comp_apply, p]
    rw [source_neck_native_center]
    exact congrArg (e.forward s hs) (neck_coordinate_inverse N hy)
  obtain ⟨A, hA⟩ := source_neck_slice_native_invertible N e s hs z.1 hp
  let v : E := A.symm w
  have hv : mfderiv (𝓡 3) (𝓡 3) f p v = w := by
    rw [← hA]
    exact A.apply_symm_apply w
  have hmetric := source_neck_slice_native_lower N e hsmall s hs hs0 hclose z.1 hz v
  let physical := F.metric (origin + s / scale)
  have hinner : 0 ≤ physical.inner (f p) w w := by
    by_cases hw : w = 0
    · simp only [hw, map_zero, le_refl]
    · exact (physical.pos (f p) w hw).le
  have hroot : (physical.tangentNorm (f p) w) ^ 2 = physical.inner (f p) w w :=
    Real.sq_sqrt hinner
  have hnorm : ‖v‖ ≤ (2 * Real.sqrt scale) * physical.tangentNorm (f p) w := by
    have hnonneg : 0 ≤ physical.tangentNorm (f p) w := Real.sqrt_nonneg _
    apply (sq_le_sq₀ (norm_nonneg v) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt e.scale_pos.le, hroot]
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ scale * physical.inner (f p)
      (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p v) at hmetric
    rw [hv] at hmetric
    nlinarith only [hmetric, mul_nonneg e.scale_pos.le hinner]
  have haxis : |cylinderHeightCovector v| ≤ ‖v‖ := PiLp.norm_apply_le v (2 : Fin 3)
  have hd := source_neck_slice_axial_mfderiv N e s hs z.1 hp v
  change mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse (e.inverse s hs y)).2) (f p)
    (mfderiv (𝓡 3) (𝓡 3) f p v) = cylinderHeightCovector v at hd
  rw [hv] at hd
  have hbound := (congrArg abs hd).trans_le (haxis.trans hnorm)
  rwa [hpoint] at hbound

end PoincareConjecture.M47
