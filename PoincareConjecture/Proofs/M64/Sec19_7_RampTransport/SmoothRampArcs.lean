import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.SmoothRampDensities













set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M64.RampTransport




theorem subarc_integral_error_of_uniform_density
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {period epsilon : ℝ} (hperiod : 0 < period) (hepsilon : 0 < epsilon)
    (herror : ∀ x, |f x - g x| < epsilon / (2 * period))
    {alpha beta : ℝ} (hab : alpha ≤ beta) (hperiodic : beta ≤ alpha + period) :
    |(∫ x in alpha..beta, f x) - ∫ x in alpha..beta, g x| < epsilon := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := alpha) (b := beta) (fun x _ =>
      show ‖f x - g x‖ ≤ epsilon / (2 * period) from (herror x).le)
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable alpha beta)
    (hg.intervalIntegrable alpha beta), Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hab)] at hbound
  have hlen : beta - alpha ≤ period := by linarith
  have hcoef : 0 ≤ epsilon / (2 * period) := by positivity
  have hhalf : epsilon / (2 * period) * period = epsilon / 2 := by
    field_simp
  exact (hbound.trans ((mul_le_mul_of_nonneg_left hlen hcoef).trans_eq hhalf)).trans_lt
    (half_lt_self hepsilon)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
  {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι




theorem exists_smooth_ramp_subarc_approximation
    (P : M62.CircleProductData F circumference)
    {time : ℝ} (htime : time ∈ Icc a b)
    {e : P.charts.Point → W} (he : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → P.charts.Point}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 (n + 1)) ∞ rho U)
    (hre : ∀ p, rho (e p) = p)
    {gamma : ℝ → P.charts.Point}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hp : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma time)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ sigma : ℝ → P.charts.Point, ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ sigma ∧
      Function.Periodic sigma curvePeriod ∧ M63IsRampAt P sigma time ∧
      (∀ x, ‖(e ∘ sigma) x - (e ∘ gamma) x‖ < epsilon ∧
        ‖deriv (e ∘ sigma) x - deriv (e ∘ gamma) x‖ < epsilon ∧
        ‖deriv (deriv (e ∘ sigma)) x - deriv (deriv (e ∘ gamma)) x‖ < epsilon) ∧
      ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
        |m63ArcLength P.flow (fun y _ => sigma y) time alpha beta -
          m63ArcLength P.flow (fun y _ => gamma y) time alpha beta| < epsilon ∧
        |m63ArcTotalCurvature P.flow (fun y _ => sigma y) time alpha beta -
          m63ArcTotalCurvature P.flow (fun y _ => gamma y) time alpha beta| < epsilon := by
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  let tolerance := min epsilon (epsilon / (2 * curvePeriod))
  have htolerance : 0 < tolerance := lt_min hepsilon (by positivity)
  obtain ⟨sigma, hsigma, hsper, hsramp, hnear, hspeed, hdensity⟩ :=
    exists_smooth_ramp_density_approximation P htime he hU heU hrho hre
      hgamma hp hramp htolerance
  have hs2 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 sigma :=
    hsigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsource := actual_curve_densities_continuous P.flow he hU heU hrho hre
    htime hgamma (M63.ramp_immersed P hramp)
  have htarget := actual_curve_densities_continuous P.flow he hU heU hrho hre
    htime hs2 (M63.ramp_immersed P hsramp)
  refine ⟨sigma, hsigma, hsper, hsramp, ?_, ?_⟩
  · intro x
    exact ⟨(hnear x).1.trans_le (min_le_left _ _),
      (hnear x).2.1.trans_le (min_le_left _ _),
      (hnear x).2.2.trans_le (min_le_left _ _)⟩
  · intro alpha beta hab hperiodic
    exact ⟨subarc_integral_error_of_uniform_density htarget.1 hsource.1 hperiod hepsilon
      (fun x => (hspeed x).trans_le (min_le_right _ _)) hab hperiodic,
      subarc_integral_error_of_uniform_density htarget.2 hsource.2 hperiod hepsilon
        (fun x => (hdensity x).trans_le (min_le_right _ _)) hab hperiodic⟩

end PoincareConjecture.M64.RampTransport
