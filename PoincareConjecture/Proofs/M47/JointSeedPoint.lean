import PoincareConjecture.Proofs.M47.JointSeedOrdinary
import PoincareConjecture.Proofs.M47.JointSeedLogarithmic
import PoincareConjecture.Proofs.M47.JointSeedPath










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M47



theorem jointSeed_action_normalization {d v A : ℝ} (hd : 0 < d)
    (hv : v ≤ d / 2) (hA : A ≤ 3 * Real.sqrt d) :
    A / (2 * Real.sqrt (d - v)) ≤ 3 / Real.sqrt 2 := by
  have ht : 0 < d - v := by linarith
  have htwo : 0 < Real.sqrt 2 := by positivity
  have hsqrt : Real.sqrt d ≤ Real.sqrt 2 * Real.sqrt (d - v) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsquare : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hmul := mul_le_mul_of_nonneg_right hsqrt htwo.le
  have hcalc : (Real.sqrt 2 * Real.sqrt (d - v)) * Real.sqrt 2 =
      2 * Real.sqrt (d - v) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt (d - v) := by ring
      _ = _ := by rw [hsquare]
  rw [hcalc] at hmul
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (d - v))).2
  apply hA.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ htwo).2
  nlinarith




theorem exists_jointSeed_point
    (P : M14OrdinaryProviders.{u} 3)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [ConnectedSpace M] [T3Space M] [SecondCountableTopology M] [CompactSpace M]
    {b t c sigma a eta : ℝ} (hbt : b < t) (hc : 0 < c) (hsigma : 0 < sigma)
    (hsigmaAge : sigma ≤ (t - b) / 2) (ha : a = sigma * Real.exp (-5 / c))
    (heta : 0 < eta) (hetaSmall : eta < a)
    (F : RicciFlow 3 M (Icc b t))
    (hscalar : ∀ s ∈ Icc b t, ∀ y : M, 0 ≤ (F.connection s).scalarCurvature y)
    (x : M) :
    ∃ _hL : LGeodesicTheory F t (t - b),
      ∃ path : BackwardTimePath F t 0 (t - b - eta),
        path.curve 0 = x ∧ IsMinimizingBackwardLPath F t 0 (t - b - eta) path ∧
        backwardLLength F t 0 (t - b - eta) path.curve ≤ 3 * Real.sqrt (t - b) ∧
        ∃ v ∈ Icc a sigma,
          v * (F.connection (b + v)).scalarCurvature (path.curve (t - b - v)) ≤ c ∧
          (F.connection (b + v)).scalarCurvature (path.curve (t - b - v)) ≤ c / a ∧
          reducedLength F t x (path.curve (t - b - v)) (t - b - v) ≤
            3 / Real.sqrt 2 := by
  let d := t - b
  have hd : 0 < d := sub_pos.mpr hbt
  have haWindow := jointSeed_age_window hc hsigma
  rw [← ha] at haWindow
  have haPos : 0 < a := haWindow.1
  have haSigma : a < sigma := haWindow.2
  have hetaD : eta < t - b := by linarith
  obtain ⟨hL, path, hstart, hmin, haction⟩ :=
    exists_jointSeed_low_action_path P hbt heta hetaD F x
  let f : ℝ → ℝ := fun v => backwardLIntegrand F t path.curve (d - v)
  let r : ℝ → ℝ := fun v =>
    (F.connection (b + v)).scalarCurvature (path.curve (d - v))
  have hfi : IntervalIntegrable f volume eta d := by
    have hi := (path.l_integrable.comp_sub_left d).symm
    have hclock : d - (t - b - eta) = eta := by dsimp [d]; ring
    simpa only [sub_zero, hclock] using hi
  have hf : ∀ v ∈ Icc eta d, 0 ≤ f v := by
    intro v hv
    apply jointSeed_integrand_nonneg path hscalar
    dsimp [d] at hv ⊢
    constructor <;> linarith [hv.1, hv.2]
  have hr (v : ℝ) (hv : v ∈ Icc a sigma) : 0 ≤ r v := by
    apply hscalar
    constructor <;> linarith [hv.1, hv.2]
  have hsc : ∀ v ∈ Icc a sigma, Real.sqrt (d / 2) * r v ≤ f v := by
    intro v hv
    have hclock : t - (d - v) = b + v := by dsimp [d]; ring
    have hsqrt : Real.sqrt (d / 2) ≤ Real.sqrt (d - v) :=
      Real.sqrt_le_sqrt (by dsimp [d]; linarith [hv.2])
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric (b + v)).toRiemannianMetric⟩
    have hkin : 0 ≤ (F.metric (b + v)).inner (path.curve (d - v))
        (curveVelocity (n := 3) path.curve (d - v))
        (curveVelocity (n := 3) path.curve (d - v)) := by
      change 0 ≤ inner ℝ (curveVelocity (n := 3) path.curve (d - v))
        (curveVelocity (n := 3) path.curve (d - v))
      exact real_inner_self_nonneg
    have hfirst := mul_le_mul_of_nonneg_right hsqrt (hr v hv)
    have hsecond := mul_nonneg (Real.sqrt_nonneg (d - v)) hkin
    dsimp [f, backwardLIntegrand]
    rw [hclock]
    dsimp [r] at hfirst
    nlinarith
  have hupper : (∫ v in eta..d, f v) ≤ 3 * Real.sqrt d := by
    change (∫ v in eta..d, backwardLIntegrand F t path.curve (d - v)) ≤ _
    rw [intervalIntegral.integral_comp_sub_left, sub_self]
    exact haction
  obtain ⟨v, hv, hvScalar⟩ := jointSeed_scalar_age_of_action hc hsigma hsigmaAge ha
    hetaSmall f r hfi hf hsc hupper
  have htheta : 0 < d - v := by dsimp [d]; linarith [hv.2]
  have hthetaPath : d - v ≤ t - b - eta := by dsimp [d]; linarith [hv.1]
  have hthetaMax : d - v ≤ t - b := by dsimp [d]; linarith [hv.1]
  let smallPath := jointSeed_restrict_path path htheta hthetaPath
  have hsmallAction : backwardLLength F t 0 (d - v) smallPath.curve ≤
      3 * Real.sqrt d :=
    (jointSeed_restricted_action_le path htheta hthetaPath hscalar).trans haction
  have hred := Proofs.M09.reducedLength_le_path hL htheta hthetaMax smallPath hstart rfl
  refine ⟨hL, path, hstart, hmin, haction, v, hv, hvScalar, ?_, ?_⟩
  · apply (le_div_iff₀ haPos).2
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right hv.1 (hr v hv)).trans hvScalar
  · exact hred.trans (jointSeed_action_normalization hd
      (hv.2.trans hsigmaAge) hsmallAction)

end PoincareConjecture.M47
