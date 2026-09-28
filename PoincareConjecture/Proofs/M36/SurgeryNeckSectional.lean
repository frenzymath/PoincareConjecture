import PoincareConjecture.Proofs.M36.ConformalPinching
import PoincareConjecture.Proofs.M36.CenteredNeckMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Pullback









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M36

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}






theorem surgeryMetric_sectional_neck_profile (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hrA : r ≤ g₀.cylindrical_end.radius)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    (Dbar : LeviCivitaData (normalizedNeckMetric N))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 1)
    (a b : TangentSpace (𝓡 3) y)
    (hpair : LeviCivitaData.IsOrthonormalPair (normalizedNeckMetric N)
      (surgeryRetainedInverse g₀ N y)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y a)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y b)) :
    let z := surgeryRetainedInverse g₀ N y
    let L := mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y
    let s := standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y)
    let u : M → ℝ := fun x => (N.coordinate_inverse x).2
    let f := smoothProfile C q N.epsilon
    D.sectionalCurvature y a b = N.connection.scalarCurvature N.center * Real.exp (2 * f s) *
      (Dbar.sectionalCurvature z (L a) (L b) +
        deriv f s * (Dbar.hessian u z (L a) (L a) + Dbar.hessian u z (L b) (L b)) +
        (deriv (deriv f) s + (deriv f s) ^ 2) *
          ((mvfderiv (𝓡 3) u z (L a)) ^ 2 + (mvfderiv (𝓡 3) u z (L b)) ^ 2) -
        (deriv f s) ^ 2 *
          (normalizedNeckMetric N).inner z (Dbar.gradient u z) (Dbar.gradient u z)) := by
  let i := surgeryBallInclusion.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)
  let T := surgeryRetainedInverse g₀ N
  let s := standardSurgeryHeight g₀ ∘ i
  let height : M → ℝ := fun x => (N.coordinate_inverse x).2
  let f := smoothProfile C q N.epsilon
  let lambda := N.connection.scalarCurvature N.center
  let E := standardCapConformalExponent g₀ C q N.epsilon r ∘ i
  let F := fun z => E z + Real.log lambda / 2
  let H := surgeryMetric g₀ N hcut C q eta r hlambda heta hr
  have hE : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ E :=
    (standardCapConformalExponent_contDiff g₀ C q N.epsilon hr).contMDiff.comp
      (surgeryBallInclusion_contMDiff g₀ _)
  have hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F := hE.add contMDiff_const
  let J := positiveScaling H (fun z => Real.exp (-2 * (-F z)))
    (contMDiff_exp_neg_two hF.neg) (fun _ => Real.exp_pos _)
  have hexp (z : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :
      Real.exp (-2 * F z) * Real.exp (-2 * (-F z)) = 1 := by
    rw [← Real.exp_add, show -2 * F z + -2 * (-F z) = 0 by ring, Real.exp_zero]
  have hback : H = positiveScaling J (fun z => Real.exp (-2 * F z))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _) := by
    have hinner : H.inner = (positiveScaling J (fun z => Real.exp (-2 * F z))
        (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)).inner := by
      funext z
      ext v w
      change H.inner z v w = Real.exp (-2 * F z) *
        (Real.exp (-2 * (-F z)) * H.inner z v w)
      rw [← mul_assoc, hexp, one_mul]
    generalize hH : H = H0 at hinner ⊢
    generalize hJ : positiveScaling J (fun z => Real.exp (-2 * F z))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _) = J0 at hinner ⊢
    cases H0
    cases J0
    cases hinner
    rfl
  obtain ⟨DJ⟩ := exists_leviCivitaData J
  let U : Set (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) := {z | s z < 5 / 4}
  have hU : IsOpen U := isOpen_lt
    ((standardSurgeryHeight_continuous g₀).comp
      (surgeryBallInclusion_contMDiff g₀ _).continuous) continuous_const
  have hyU : y ∈ U := lt_of_le_of_lt hy (by norm_num)
  have hne : ∀ z ∈ U, i z ≠ 0 := by
    intro z hz hzero
    change standardSurgeryHeight g₀ (i z) < 5 / 4 at hz
    rw [hzero, standardSurgeryHeight_zero] at hz
    linarith [g₀.cylindrical_end.radius_pos]
  have hT (z : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) (hz : z ∈ U) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ T z :=
    surgeryRetainedInverse_contMDiffAt g₀ N hcut (hne z hz)
  have hcancel (z : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :
      Real.exp (-2 * (-F z)) * surgeryConformalMultiplier g₀ N C q r z = lambda := by
    change Real.exp (-2 * (-F z)) * radialConformalMultiplier g₀ C q N.epsilon r (i z) = lambda
    rw [← standardCapConformalExponent_exp g₀ C q N.epsilon r (i z)]
    change Real.exp (-2 * (-(E z + Real.log lambda / 2))) * Real.exp (-2 * E z) = lambda
    rw [← Real.exp_add,
      show -2 * (-(E z + Real.log lambda / 2)) + -2 * E z = Real.log lambda by ring,
      Real.exp_log hlambda]
  have hmetric : ∀ z ∈ U, ∀ v w : TangentSpace (𝓡 3) z,
      J.inner z v w = (normalizedNeckMetric N).inner (T z)
        (mfderiv (𝓡 3) (𝓡 3) T z v) (mfderiv (𝓡 3) (𝓡 3) T z w) := by
    intro z hz v w
    have hweight : surgeryNeckWeight g₀ N z = 1 := neckCutoff_eq_one (le_of_lt hz)
    change Real.exp (-2 * (-F z)) * H.inner z v w = _
    rw [surgeryMetric_inner, hweight]
    simp only [one_mul, sub_self, zero_mul, add_zero]
    change Real.exp (-2 * (-F z)) * (surgeryConformalMultiplier g₀ N C q r z *
      g.inner (T z) (mfderiv (𝓡 3) (𝓡 3) T z v) (mfderiv (𝓡 3) (𝓡 3) T z w)) =
      lambda * g.inner (T z) (mfderiv (𝓡 3) (𝓡 3) T z v) (mfderiv (𝓡 3) (𝓡 3) T z w)
    rw [← mul_assoc, hcancel]
  have hmetricGerm : ∀ᶠ z in nhds y, ∀ v w : TangentSpace (𝓡 3) z,
      J.inner z v w = (normalizedNeckMetric N).inner (T z)
        (mfderiv (𝓡 3) (𝓡 3) T z v) (mfderiv (𝓡 3) (𝓡 3) T z w) := by
    filter_upwards [hU.mem_nhds hyU] with z hz using hmetric z hz
  have hinv : ∀ᶠ z in nhds y, (mfderiv (𝓡 3) (𝓡 3) T z).IsInvertible := by
    filter_upwards [hU.mem_nhds hyU] with z hz
    have hb := surgeryRetainedInverse_mfderiv_bijective g₀ N hcut (hne z hz)
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) z) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) → Type _) z
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (T z)) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) (T z)
    let : T2Space (TangentSpace (𝓡 3) z) :=
      FiberBundle.t2Space (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) z
    let : T2Space (TangentSpace (𝓡 3) (T z)) :=
      FiberBundle.t2Space (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) (T z)
    exact ⟨(LinearEquiv.ofBijective
      (mfderiv (𝓡 3) (𝓡 3) T z).toLinearMap hb).toContinuousLinearEquiv, rfl⟩
  have hheight : height ∘ T = s := by
    funext z
    exact surgeryRetainedInverse_height g₀ N hcut z
  have hu : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ height (T y) :=
    (neck_inverse_contMDiffAt N (surgeryRetainedInverse_mem g₀ N hcut y)).snd
  have hs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ s y := by
    rw [← hheight]
    exact hu.comp y (hT y hyU)
  have hd (v : TangentSpace (𝓡 3) y) :
      mvfderiv (𝓡 3) s y v =
        mvfderiv (𝓡 3) height (T y) (mfderiv (𝓡 3) (𝓡 3) T y v) := by
    rw [← hheight, mvfderiv_comp y (hu.mdifferentiableAt (by simp))
      ((hT y hyU).mdifferentiableAt (by simp))]
    rfl
  have hHess (v w : TangentSpace (𝓡 3) y) :
      DJ.hessian s y v w = Dbar.hessian height (T y)
        (mfderiv (𝓡 3) (𝓡 3) T y v) (mfderiv (𝓡 3) (𝓡 3) T y w) := by
    rw [← hheight]
    exact DJ.hessian_comp_of_metric_pullback Dbar (hT y hyU) hinv hmetricGerm hu v w
  have hgrad : J.inner y (DJ.gradient s y) (DJ.gradient s y) =
      (normalizedNeckMetric N).inner (T y)
        (Dbar.gradient height (T y)) (Dbar.gradient height (T y)) := by
    rw [← hheight, DJ.gradient_comp_eq_mpullback Dbar
      ((hT y hyU).mdifferentiableAt (by simp)) (hu.mdifferentiableAt (by simp))
      hinv.self_of_nhds (hmetric y hyU), hmetric y hyU]
    simp only [VectorField.mpullback, hinv.self_of_nhds.self_apply_inverse]
  have hpairJ : LeviCivitaData.IsOrthonormalPair J y a b := by
    unfold LeviCivitaData.IsOrthonormalPair
    rw [hmetric y hyU, hmetric y hyU, hmetric y hyU]
    exact hpair
  have heq : F =ᶠ[nhds y] fun z => f (s z) + Real.log lambda / 2 := by
    filter_upwards [hU.mem_nhds hyU] with z hz
    change standardCapConformalExponent g₀ C q N.epsilon r (i z) + Real.log lambda / 2 = _
    rw [standardCapConformalExponent_eq_on_transition g₀ C q N.epsilon hr hrA
      (by change s z ≤ 2; change s z < 5 / 4 at hz; linarith only [hz])]
    rfl
  have hprofile : D.sectionalCurvature y a b = Real.exp (2 * (f (s y) + Real.log lambda / 2)) *
      (DJ.sectionalCurvature y a b +
        deriv f (s y) * (DJ.hessian s y a a + DJ.hessian s y b b) +
        (deriv (deriv f) (s y) + (deriv f (s y)) ^ 2) *
          ((mvfderiv (𝓡 3) s y a) ^ 2 + (mvfderiv (𝓡 3) s y b) ^ 2) -
        (deriv f (s y)) ^ 2 * J.inner y (DJ.gradient s y) (DJ.gradient s y)) := by
    change LeviCivitaData H at D
    change D.sectionalCurvature (g := H) y a b = _
    revert D
    rw [hback]
    intro D
    have hformula := sectionalCurvature_positiveScaling_profile J DJ F hF D s
      (fun t => f t + Real.log lambda / 2)
      ((smoothProfile_contDiff C q N.epsilon).add contDiff_const) y hs heq
      a b hpairJ.1 hpairJ.2.1 hpairJ.2.2
    simpa only [deriv_add_const', deriv_add_const] using hformula
  have hfactor : Real.exp (2 * (f (s y) + Real.log lambda / 2)) =
      lambda * Real.exp (2 * f (s y)) := by
    rw [show 2 * (f (s y) + Real.log lambda / 2) = Real.log lambda + 2 * f (s y) by ring,
      Real.exp_add, Real.exp_log hlambda]
  rw [hfactor, sectionalCurvature_eq_of_local_isometry DJ Dbar hU
    (fun z hz => (hT z hz).contMDiffWithinAt) hmetric hyU,
    hHess a a, hHess b b, hd a, hd b, hgrad] at hprofile
  exact hprofile




theorem surgeryMetric_orthonormal_neck_profile (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hrA : r ≤ g₀.cylindrical_end.radius)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 1)
    (a b : TangentSpace (𝓡 3) y)
    (hab : LeviCivitaData.IsOrthonormalPair
      (surgeryMetric g₀ N hcut C q eta r hlambda heta hr) y a b) :
    let c := Real.exp (-(smoothProfile C q N.epsilon
      (standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y)) +
      Real.log (N.connection.scalarCurvature N.center) / 2))
    LeviCivitaData.IsOrthonormalPair (normalizedNeckMetric N)
      (surgeryRetainedInverse g₀ N y)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y (c • a))
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y (c • b)) := by
  let s := standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y)
  let f := smoothProfile C q N.epsilon s
  let lambda := N.connection.scalarCurvature N.center
  let c := Real.exp (-(f + Real.log lambda / 2))
  let T := surgeryRetainedInverse g₀ N
  let L := mfderiv (𝓡 3) (𝓡 3) T y
  have he : lambda * (c * c) = Real.exp (-2 * f) := by
    have hlog : Real.exp (Real.log lambda) = lambda := Real.exp_log hlambda
    rw [← hlog]
    change Real.exp (Real.log lambda) *
      (Real.exp (-(f + Real.log lambda / 2)) * Real.exp (-(f + Real.log lambda / 2))) = _
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hweight : surgeryNeckWeight g₀ N y = 1 :=
    neckCutoff_eq_one (hy.trans (by norm_num))
  have hmult : surgeryConformalMultiplier g₀ N C q r y = Real.exp (-2 * f) := by
    change radialConformalMultiplier g₀ C q N.epsilon r (surgeryBallInclusion g₀ _ y) = _
    exact radialConformalMultiplier_eq_on_transition g₀ C q N.epsilon hr hrA
      (hy.trans (by norm_num))
  have hm (v w : TangentSpace (𝓡 3) y) :
      (normalizedNeckMetric N).inner (T y) (L (c • v)) (L (c • w)) =
        (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner y v w := by
    rw [surgeryMetric_inner, hweight, hmult]
    simp only [one_mul, sub_self, zero_mul, add_zero, metricPullbackForm_apply]
    change lambda * g.inner (T y) (L (c • v)) (L (c • w)) = _
    simp only [map_smul, smul_apply, smul_eq_mul]
    calc
      _ = (lambda * (c * c)) * g.inner (T y) (L v) (L w) := by ring
      _ = _ := by rw [he]
  exact ⟨(hm a a).trans hab.1, (hm b b).trans hab.2.1, (hm a b).trans hab.2.2⟩





theorem surgeryMetric_negativeCurvaturePart_neck_le (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hrA : r ≤ g₀.cylindrical_end.radius)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    (Dbar : LeviCivitaData (normalizedNeckMetric N))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 1) :
    let z := surgeryRetainedInverse g₀ N y
    let s := standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y)
    let height : M → ℝ := fun x => (N.coordinate_inverse x).2
    let f := smoothProfile C q N.epsilon
    ∀ B kappa : ℝ, 0 ≤ deriv f s → 0 ≤ deriv (deriv f) s →
      (∀ v : TangentSpace (𝓡 3) z, (normalizedNeckMetric N).inner z v v = 1 →
        -B ≤ Dbar.hessian height z v v) →
      (normalizedNeckMetric N).inner z (Dbar.gradient height z) (Dbar.gradient height z) ≤ 2 →
      2 * B * deriv f s + 2 * (deriv f s) ^ 2 ≤ deriv (deriv f) s / 4 →
      (∀ v w : TangentSpace (𝓡 3) z,
        LeviCivitaData.IsOrthonormalPair (normalizedNeckMetric N) z v w →
        (mvfderiv (𝓡 3) height z v) ^ 2 + (mvfderiv (𝓡 3) height z w) ^ 2 < 1 / 2 →
          kappa ≤ Dbar.sectionalCurvature z v w) →
      2 * B * deriv f s + 2 * (deriv f s) ^ 2 ≤ kappa →
      2 * Dbar.negativeCurvaturePart z * f s ≤ deriv (deriv f) s / 4 →
        D.negativeCurvaturePart y ≤ N.connection.negativeCurvaturePart z := by
  dsimp only
  intro B kappa hp ht hH hG herr hgap hsmall hamp
  let z := surgeryRetainedInverse g₀ N y
  let s := standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y)
  let height : M → ℝ := fun x => (N.coordinate_inverse x).2
  let f := smoothProfile C q N.epsilon
  let p := deriv f s
  let t := deriv (deriv f) s
  let lambda := N.connection.scalarCurvature N.center
  let X := Dbar.negativeCurvaturePart z
  let c := Real.exp (-(f s + Real.log lambda / 2))
  let L := mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y
  change 0 ≤ p at hp
  have hX : 0 ≤ X := le_max_right _ _
  have hscale : lambda * X = N.connection.negativeCurvaturePart z := by
    have he := negativeCurvaturePart_positiveScaling_const N.connection hlambda Dbar z
    change X = lambda⁻¹ * N.connection.negativeCurvaturePart z at he
    rw [he, ← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul]
  apply negativeCurvaturePart_le_of_sectional_lower_bound D y (le_max_right _ _)
  intro a b hab
  let v := L (c • a)
  let w := L (c • b)
  let A := (mvfderiv (𝓡 3) height z v) ^ 2 + (mvfderiv (𝓡 3) height z w) ^ 2
  let K := Dbar.sectionalCurvature z v w
  let Q := K + p * (Dbar.hessian height z v v + Dbar.hessian height z w w) +
    (t + p ^ 2) * A - p ^ 2 *
      (normalizedNeckMetric N).inner z (Dbar.gradient height z) (Dbar.gradient height z)
  have hbase : LeviCivitaData.IsOrthonormalPair (normalizedNeckMetric N) z v w :=
    surgeryMetric_orthonormal_neck_profile g₀ N hcut C q eta r hlambda heta hr hrA hy a b hab
  have hformula := surgeryMetric_sectional_neck_profile g₀ N hcut C q eta r
    hlambda heta hr hrA D Dbar hy (c • a) (c • b) hbase
  change D.sectionalCurvature y (c • a) (c • b) = lambda * Real.exp (2 * f s) * Q at hformula
  rw [sectionalCurvature_smul_pair D y a b (Real.exp_ne_zero _) (Real.exp_ne_zero _)] at hformula
  have hA0 : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hK : -X ≤ K := neg_negativeCurvaturePart_le_sectional_of_orthonormal Dbar z hbase
  have hHa := mul_le_mul_of_nonneg_left (hH v hbase.1) hp
  have hHb := mul_le_mul_of_nonneg_left (hH w hbase.2.1) hp
  have hG' := mul_le_mul_of_nonneg_left hG (sq_nonneg p)
  have hL : K + t * A - 2 * B * p - 2 * p ^ 2 ≤ Q := by
    dsimp only [Q]
    nlinarith only [hHa, hHb, hG', mul_nonneg (sq_nonneg p) hA0]
  change 0 ≤ t at ht
  change 2 * B * p + 2 * p ^ 2 ≤ t / 4 at herr
  change 2 * B * p + 2 * p ^ 2 ≤ kappa at hsmall
  change 2 * X * f s ≤ t / 4 at hamp
  have hbound : -X ≤ Real.exp (2 * f s) * Q := by
    by_cases hA : 1 / 2 ≤ A
    · have hta := mul_le_mul_of_nonneg_left hA ht
      have hgain : -X + t / 4 ≤ Q := by nlinarith only [hK, hta, herr, hL]
      have hnegative := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (2 * f s)) hX
      have hcomp : -X * Real.exp (-(2 * f s)) ≤ -X + t / 4 := by
        nlinarith only [hnegative, hamp]
      have hcancel : Real.exp (2 * f s) * Real.exp (-(2 * f s)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc
        -X = Real.exp (2 * f s) * (-X * Real.exp (-(2 * f s))) := by
          calc
            -X = -X * (Real.exp (2 * f s) * Real.exp (-(2 * f s))) := by
              rw [hcancel, mul_one]
            _ = _ := by ring
        _ ≤ Real.exp (2 * f s) * Q :=
          mul_le_mul_of_nonneg_left (hcomp.trans hgain) (Real.exp_pos _).le
    · have hbasegap : kappa ≤ K := hgap v w hbase (lt_of_not_ge hA)
      have hQ : 0 ≤ Q := by nlinarith only [hbasegap, hsmall, hL, mul_nonneg ht hA0]
      exact (neg_nonpos.mpr hX).trans (mul_nonneg (Real.exp_pos _).le hQ)
  change -N.connection.negativeCurvaturePart z ≤ D.sectionalCurvature y a b
  rw [hformula, ← hscale]
  calc
    -(lambda * X) = lambda * (-X) := by ring
    _ ≤ lambda * (Real.exp (2 * f s) * Q) := mul_le_mul_of_nonneg_left hbound hlambda.le
    _ = _ := by ring




theorem surgeryMetric_sectional_neck_pos (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hrA : r ≤ g₀.cylindrical_end.radius)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    (Dbar : LeviCivitaData (normalizedNeckMetric N))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 1) :
    let z := surgeryRetainedInverse g₀ N y
    let s := standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y)
    let height : M → ℝ := fun x => (N.coordinate_inverse x).2
    let f := smoothProfile C q N.epsilon
    ∀ B kappa : ℝ, 0 ≤ deriv f s → 0 ≤ deriv (deriv f) s →
      (∀ v : TangentSpace (𝓡 3) z, (normalizedNeckMetric N).inner z v v = 1 →
        -B ≤ Dbar.hessian height z v v) →
      (normalizedNeckMetric N).inner z (Dbar.gradient height z) (Dbar.gradient height z) ≤ 2 →
      2 * B * deriv f s + 2 * (deriv f s) ^ 2 ≤ deriv (deriv f) s / 4 →
      (∀ v w : TangentSpace (𝓡 3) z,
        LeviCivitaData.IsOrthonormalPair (normalizedNeckMetric N) z v w →
        (mvfderiv (𝓡 3) height z v) ^ 2 + (mvfderiv (𝓡 3) height z w) ^ 2 < 1 / 2 →
          kappa ≤ Dbar.sectionalCurvature z v w) →
      2 * B * deriv f s + 2 * (deriv f s) ^ 2 < kappa →
      (∀ v w : TangentSpace (𝓡 3) z, LeviCivitaData.IsOrthonormalPair g z v w →
        0 < N.connection.sectionalCurvature z v w) →
      ∀ a b : TangentSpace (𝓡 3) y, LeviCivitaData.IsOrthonormalPair
        (surgeryMetric g₀ N hcut C q eta r hlambda heta hr) y a b →
        0 < D.sectionalCurvature y a b := by
  dsimp only
  intro B kappa hp ht hH hG herr hgap hsmall hpositive a b hab
  let z := surgeryRetainedInverse g₀ N y
  let s := standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y)
  let height : M → ℝ := fun x => (N.coordinate_inverse x).2
  let f := smoothProfile C q N.epsilon
  let p := deriv f s
  let t := deriv (deriv f) s
  let lambda := N.connection.scalarCurvature N.center
  let c := Real.exp (-(f s + Real.log lambda / 2))
  let L := mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y
  let v := L (c • a)
  let w := L (c • b)
  let A := (mvfderiv (𝓡 3) height z v) ^ 2 + (mvfderiv (𝓡 3) height z w) ^ 2
  let K := Dbar.sectionalCurvature z v w
  let Q := K + p * (Dbar.hessian height z v v + Dbar.hessian height z w w) +
    (t + p ^ 2) * A - p ^ 2 *
      (normalizedNeckMetric N).inner z (Dbar.gradient height z) (Dbar.gradient height z)
  have hbase : LeviCivitaData.IsOrthonormalPair (normalizedNeckMetric N) z v w :=
    surgeryMetric_orthonormal_neck_profile g₀ N hcut C q eta r hlambda heta hr hrA hy a b hab
  have hinput := (positiveScaling_const_orthonormal_iff g hlambda z v w).mp hbase
  have hconst : Dbar.sectionalCurvature z (Real.sqrt lambda • v) (Real.sqrt lambda • w) =
      lambda⁻¹ * N.connection.sectionalCurvature z (Real.sqrt lambda • v) (Real.sqrt lambda • w) :=
    sectionalCurvature_positiveScaling_const_of_orthonormal N.connection hlambda Dbar z hinput
  have hsqrt : Real.sqrt lambda ≠ 0 := (Real.sqrt_pos.mpr hlambda).ne'
  rw [sectionalCurvature_smul_pair Dbar z v w
    hsqrt hsqrt] at hconst
  have hK : 0 < K := by
    change 0 < Dbar.sectionalCurvature z v w
    rw [hconst]
    exact mul_pos (inv_pos.mpr hlambda) (hpositive _ _ hinput)
  have hformula := surgeryMetric_sectional_neck_profile g₀ N hcut C q eta r
    hlambda heta hr hrA D Dbar hy (c • a) (c • b) hbase
  change D.sectionalCurvature y (c • a) (c • b) = lambda * Real.exp (2 * f s) * Q at hformula
  rw [sectionalCurvature_smul_pair D y a b (Real.exp_ne_zero _) (Real.exp_ne_zero _)] at hformula
  change 0 ≤ p at hp
  have hA0 : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hHa := mul_le_mul_of_nonneg_left (hH v hbase.1) hp
  have hHb := mul_le_mul_of_nonneg_left (hH w hbase.2.1) hp
  have hG' := mul_le_mul_of_nonneg_left hG (sq_nonneg p)
  have hL : K + t * A - 2 * B * p - 2 * p ^ 2 ≤ Q := by
    dsimp only [Q]
    nlinarith only [hHa, hHb, hG', mul_nonneg (sq_nonneg p) hA0]
  change 0 ≤ t at ht
  change 2 * B * p + 2 * p ^ 2 ≤ t / 4 at herr
  change 2 * B * p + 2 * p ^ 2 < kappa at hsmall
  have hQ : 0 < Q := by
    by_cases hA : 1 / 2 ≤ A
    · have hta := mul_le_mul_of_nonneg_left hA ht
      nlinarith only [hK, ht, hta, herr, hL]
    · have hbasegap : kappa ≤ K := hgap v w hbase (lt_of_not_ge hA)
      nlinarith only [hbasegap, hsmall, hL, mul_nonneg ht hA0]
  rw [hformula]
  exact mul_pos (mul_pos hlambda (Real.exp_pos _)) hQ


end PoincareConjecture.M36
