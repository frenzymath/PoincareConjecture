import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CanonicalRampRegularity
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Def19_12_PositiveDegree
import PoincareConjecture.Proofs.M62.Sec19_3_CircleIdentities
import PoincareConjecture.Proofs.M04.ShiEnergyPaths










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}



theorem canonicalRamp_speed (P : M62.CircleProductData F circumference)
    {gamma : ℝ → M} {x : ℝ} (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma x)
    (t : ℝ) :
    curveSpeed P.flow (fun y _ => m63CanonicalRamp P gamma y) t x =
      Real.sqrt (curveSpeed F (fun y _ => gamma y) t x ^ 2 +
        (circumference / curvePeriod) ^ 2) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hnonneg : 0 ≤ (F.metric t).inner (gamma x) (curveVelocity gamma x)
      (curveVelocity gamma x) := by
    by_cases hz : curveVelocity (n := n) gamma x = 0
    · simp [hz]
    · exact ((F.metric t).pos _ _ hz).le
  unfold curveSpeed RiemannianMetric.tangentNorm
  rw [P.metric_eq, canonicalRamp_velocity P hgamma]
  simp only [map_smul, smul_apply, smul_eq_mul,
    (M62.circle_identities P.circle).frame_unit, mul_one]
  rw [Real.sq_sqrt hnonneg]
  congr 1
  dsimp only [m63CanonicalRamp]
  ring



theorem canonicalRamp_speed_pos (P : M62.CircleProductData F circumference)
    {gamma : ℝ → M} {x : ℝ} (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma x)
    (t : ℝ) : 0 < curveSpeed P.flow (fun y _ => m63CanonicalRamp P gamma y) t x := by
  rw [canonicalRamp_speed P hgamma]
  apply Real.sqrt_pos.mpr
  have hA : 0 < circumference / curvePeriod := div_pos P.circle.positive Real.two_pi_pos
  nlinarith [sq_nonneg (curveSpeed F (fun y _ => gamma y) t x), sq_pos_of_pos hA]



theorem canonicalRamp_isRamp (P : M62.CircleProductData F circumference)
    {gamma : ℝ → M} (hgamma : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) gamma) (t : ℝ) :
    M63IsRampAt P (m63CanonicalRamp P gamma) t := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let phi : ℝ → ℝ := fun x => circumference * x / curvePeriod
  have hphi : Differentiable ℝ phi :=
    ((differentiable_const circumference).mul differentiable_id).div_const _
  have hgraph : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (m63CanonicalRamp P gamma) :=
    (P.charts.from_product_smooth.mdifferentiable (by simp)).comp
      (hgamma.prodMk ((P.circle.quotient_smooth.mdifferentiable (by simp)).comp
        hphi.mdifferentiable))
  intro x
  rw [m63Slope_eq_lift_deriv_div_speed P hgraph hphi (fun _ => rfl)]
  have hd : HasDerivAt phi (circumference / curvePeriod) x := by
    simpa [phi] using ((hasDerivAt_id x).const_mul circumference).div_const curvePeriod
  rw [hd.deriv]
  exact div_pos (div_pos P.circle.positive Real.two_pi_pos)
    (canonicalRamp_speed_pos P (hgamma x) t)



theorem canonicalRamp_length_le (P : M62.CircleProductData F circumference)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma) (t : ℝ) :
    m62Length P.flow (fun x _ => m63CanonicalRamp P gamma x) t ≤
      m62Length F (fun x _ => gamma x) t + circumference := by
  let := P.charts.chartedSpace
  let v : ℝ → ℝ := fun x => curveSpeed F (fun y _ => gamma y) t x
  let w : ℝ → ℝ := fun x => curveSpeed P.flow (fun y _ => m63CanonicalRamp P gamma y) t x
  have hv : Continuous v := M04.continuous_pathSpeed (F.metric t) hgamma
  have hw : Continuous w := M04.continuous_pathSpeed (P.flow.metric t)
    (canonicalRamp_contMDiff P (by decide) hgamma)
  have hA : 0 < circumference / curvePeriod := div_pos P.circle.positive Real.two_pi_pos
  have hpoint (x : ℝ) : w x ≤ v x + circumference / curvePeriod := by
    rw [show w x = Real.sqrt (v x ^ 2 + (circumference / curvePeriod) ^ 2) from
      canonicalRamp_speed P (hgamma.mdifferentiableAt (by norm_num)) t]
    have hvx : 0 ≤ v x := Real.sqrt_nonneg _
    exact Real.sqrt_le_iff.mpr ⟨add_nonneg hvx hA.le, by nlinarith⟩
  have hmono : (∫ x in (0 : ℝ)..curvePeriod, w x) ≤
      ∫ x in (0 : ℝ)..curvePeriod, v x + circumference / curvePeriod :=
    intervalIntegral.integral_mono (μ := MeasureTheory.volume)
      (show (0 : ℝ) ≤ curvePeriod from Real.two_pi_pos.le)
      (hw.intervalIntegrable 0 curvePeriod)
      ((hv.intervalIntegrable 0 curvePeriod).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add (hv.intervalIntegrable 0 curvePeriod) intervalIntegrable_const,
    intervalIntegral.integral_const] at hmono
  have hconstant : curvePeriod * (circumference / curvePeriod) = circumference := by
    have hperiod : curvePeriod ≠ 0 := ne_of_gt Real.two_pi_pos
    field_simp
  change (∫ x in (0 : ℝ)..curvePeriod, w x) ≤ (∫ x in (0 : ℝ)..curvePeriod, v x) + circumference
  simpa only [sub_zero, smul_eq_mul, hconstant] using hmono

end PoincareConjecture.M63
