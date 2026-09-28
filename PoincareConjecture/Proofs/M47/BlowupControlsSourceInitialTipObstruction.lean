import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNativeRicci
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSliceChart









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



theorem source_neck_slice_not_tip_ricci_lower
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    {origin scale : ℝ} {I : Set ℝ}
    (e : SurgeryFlowCylinder F C origin scale I N.carrier)
    (hsmall : N.epsilon ≤ 1 / 1200) (s : ℝ) (hs : s ∈ I) (hs0 : s ≤ 0)
    (hclose : RoundCylinderClose N.epsilon s (surgeryCylinderPullback e N.coordinate_map s))
    {mu K h : ℝ} (hmu : 0 < mu) (hK : 0 < K) (hh : 0 < h)
    (hscale : scale * h ^ 2 ≤ 4 * K)
    (htolerance : N.epsilon ≤ mu / (1024 * (K + 1)))
    {x : (F.slice (origin + s / scale)).carrier}
    (hx : x ∈ e.forward s hs '' N.carrier)
    (hRicci : ∀ w : TangentSpace (𝓡 3) x,
      (mu / h ^ 2) * (F.metric (origin + s / scale)).inner x w w ≤
        (F.connection (origin + s / scale)).ricci x w w) : False := by
  obtain ⟨y, hy, rfl⟩ := hx
  let z := N.coordinate_inverse y
  let p := M35.cylinderCoordinateEquiv.symm ((0, z.2) : RoundCylinderCoordinates)
  let f := e.forward s hs ∘ centeredNeckLift N z.1 0
  let v := EuclideanSpace.basisFun (Fin 3) ℝ 2
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (N.coordinate_inverse_mem y hy).2
  have hp : p ∈ centeredNeckDomain N 0 := by
    change (M35.cylinderCoordinateEquiv p).2 + 0 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply, add_zero] using hz
  have hpoint : f p = e.forward s hs y := by
    dsimp only [f, Function.comp_apply, p]
    rw [source_neck_native_center]
    exact congrArg (e.forward s hs) (neck_coordinate_inverse N hy)
  obtain ⟨g1, D1, W, hW, hpW, hcoeff, _hscalar⟩ :=
    source_neck_slice_metric_realization N e s hs z.1 hz
  have htime : s < 1 := hs0.trans_lt (by norm_num)
  let D0 := D1.withMetric (M35.cylinderEuclideanMetric s htime)
  obtain ⟨hupper, hmetricLower⟩ := source_initial_native_axial_bounds N.epsilon_pos
    (show N.epsilon ≤ 1 / 2 by linarith only [hsmall]) htime
    (surgeryCylinderPullback e N.coordinate_map s) hclose g1 D1 D0 z.1 hW hcoeff z.2 hz hpW
  have hmetric := source_neck_slice_metric_of_coefficients N e s hs z.1 g1 hp
    (hcoeff p hpW) v v
  have hricci := source_neck_slice_ricci_of_coefficients N e s hs z.1 g1 D1 hW hcoeff hpW hp v v
  have hphysical : ∀ w : TangentSpace (𝓡 3) (f p),
      (mu / h ^ 2) * (F.metric (origin + s / scale)).inner (f p) w w ≤
        (F.connection (origin + s / scale)).ricci (f p) w w := hpoint.symm ▸ hRicci
  have hlower := hphysical (mfderiv (𝓡 3) (𝓡 3) f p v)
  rw [← hricci] at hlower
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  have hprod : 0 < scale * h ^ 2 := mul_pos e.scale_pos hsq
  have hnormalized : (mu / (scale * h ^ 2)) * g1.inner p v v ≤ D1.ricci p v v := by
    rw [hmetric]
    convert hlower using 1
    field_simp [e.scale_pos.ne', hsq.ne']
    rfl
  have hdiv : mu / (4 * K) ≤ mu / (scale * h ^ 2) :=
    div_le_div_of_nonneg_left hmu.le hprod hscale
  have hpositive : mu / (8 * K) ≤ D1.ricci p v v := by
    calc
      _ = (mu / (4 * K)) * (1 / 2) := by ring
      _ ≤ (mu / (scale * h ^ 2)) * (1 / 2) :=
        mul_le_mul_of_nonneg_right hdiv (by norm_num)
      _ ≤ (mu / (scale * h ^ 2)) * g1.inner p v v :=
        mul_le_mul_of_nonneg_left hmetricLower (div_pos hmu hprod).le
      _ ≤ _ := hnormalized
  have hpoly : 54 * N.epsilon + 2430 * N.epsilon ^ 2 ≤ 57 * N.epsilon := by
    have hsquare := mul_le_mul_of_nonneg_left hsmall N.epsilon_pos.le
    nlinarith only [hsquare, N.epsilon_pos]
  have hmargin : 57 * N.epsilon < mu / (8 * K) := by
    apply (lt_div_iff₀ (show 0 < 8 * K by positivity)).mpr
    have hmul := (le_div_iff₀ (show 0 < 1024 * (K + 1) by positivity)).mp htolerance
    nlinarith only [hmul, N.epsilon_pos, mul_pos N.epsilon_pos hK]
  exact not_lt_of_ge hpositive
    (((le_abs_self (D1.ricci p v v)).trans (hupper.trans hpoly)).trans_lt hmargin)

end PoincareConjecture.M47
