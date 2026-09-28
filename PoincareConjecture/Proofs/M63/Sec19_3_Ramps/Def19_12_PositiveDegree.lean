import PoincareConjecture.Proofs.M63.Mathlib.CircleLift
import PoincareConjecture.Proofs.M63.Mathlib.LocalDiffeomorphLift
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.SlopeRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem m63CircleLift_contDiff {p : ℝ} (C : M62.CircleGeometry p)
    {f : ℝ → C.Point} (hf : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 2 f)
    {L : ℝ → ℝ} (hL : Continuous L) (hquot : ∀ x, C.quotient (L x) = f x) :
    ContDiff ℝ 2 L := by
  let := C.chartedSpace
  apply contMDiff_iff_contDiff.mp
  intro x
  have hp : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ C.quotient (L x) :=
    C.quotient_local_diffeomorph (L x)
  apply hp.contMDiffAt_of_comp (I := 𝓘(ℝ, ℝ)) (m := 2) (by decide) hL.continuousAt
  rw [show C.quotient ∘ L = f from funext hquot]
  exact hf x

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63Slope_eq_lift_deriv_div_speed
    {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) {gamma : ℝ → P.charts.Point}
    (hgamma : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma)
    {L : ℝ → ℝ} (hL : Differentiable ℝ L)
    (hquot : ∀ x, P.circle.quotient (L x) = (gamma x).2) (t x : ℝ) :
    m62Slope P (fun y _ => gamma y) t x =
      deriv L x / curveSpeed P.flow (fun y _ => gamma y) t x := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hsnd : MDifferentiable (𝓡 (n + 1)) (𝓡 1)
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiable (by simp)
  have hpr := mfderiv_comp_apply (f := gamma)
    (g := (Prod.snd : P.charts.Point → P.circle.Point)) x (hsnd (gamma x)) (hgamma x) 1
  have hval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) L x 1 = deriv L x := by
    rw [mfderiv_eq_fderiv, (hL x).hasDerivAt.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  have hl := mfderiv_comp_apply (f := L) (g := P.circle.quotient) x
    (P.circle.quotient_smooth.mdifferentiableAt (by simp))
    (hL x).hasDerivAt.hasFDerivAt.hasMFDerivAt.mdifferentiableAt 1
  have heq : P.circle.quotient ∘ L = Prod.snd ∘ gamma := funext hquot
  rw [heq, hval] at hl
  have hv : (P.charts.split (gamma x) (curveVelocity gamma x)).2 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient (L x) (deriv L x) := by
    rw [P.charts.split_circle]
    exact hpr.symm.trans hl
  have hpair : (P.flow.metric t).inner (gamma x) (curveVelocity gamma x)
      (P.charts.circleUnit (gamma x)) = deriv L x := by
    rw [P.metric_eq]
    simp only [M62.CircleProductCharts.circleUnit, ContinuousLinearEquiv.apply_symm_apply,
      map_zero, zero_add]
    have hframe : P.circle.frame (P.circle.quotient (L x)) =
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient (L x) 1 := P.circle.frame_quotient (L x)
    rw [hv, ← hquot x, hframe]
    simpa +instances only [M62.CircleGeometry.quotient, M62.CircleGeometry.metricOnPoints,
      mul_one] using! P.circle.metric_quotient (L x) (deriv L x) 1
  simp only [m62Slope, spatialUnitTangent, map_smul, smul_apply, smul_eq_mul]
  rw [hpair]
  rw [div_eq_mul_inv, mul_comm]

theorem m63PositiveDegreeLift_nonempty
    {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (gamma : ℝ → P.charts.Point)
    (hper : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    {t : ℝ} (hramp : M63IsRampAt P gamma t) :
    Nonempty (M63PositiveDegreeLift P gamma) := by
  let := P.charts.chartedSpace
  have hproj : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 2 (fun x => (gamma x).2) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).of_le (by decide) |>.comp hgamma
  obtain ⟨L, hL, hquot⟩ := AddCircle.exists_continuous_real_lift hproj.continuous
  have hregular := m63CircleLift_contDiff P.circle hproj hL hquot
  have hpositive (x : ℝ) : 0 < deriv L x := by
    have h := hramp x
    rw [m63Slope_eq_lift_deriv_div_speed P (hgamma.mdifferentiable (by norm_num))
      (hregular.differentiable (by norm_num)) hquot] at h
    have hv : 0 ≤ curveSpeed P.flow (fun y _ => gamma y) t x := Real.sqrt_nonneg _
    rcases (div_pos_iff.mp h) with h | h
    · exact h.1
    · exact (not_lt_of_ge hv h.2).elim
  have hperL : Function.Periodic (fun x => (L x : AddCircle circumference)) curvePeriod := by
    intro x
    change (L (x + curvePeriod) : AddCircle circumference) = (L x : AddCircle circumference)
    rw [hquot, hquot, hper x]
  obtain ⟨N, hN, hshift⟩ := AddCircle.real_lift_positive_degree P.circle.positive
    (by unfold curvePeriod; positivity) hL hpositive hperL
  exact ⟨⟨L, hregular, N, hN, hquot, hshift, hpositive⟩⟩

end PoincareConjecture
