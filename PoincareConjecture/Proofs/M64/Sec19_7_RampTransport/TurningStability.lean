import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.SmoothRampArcs













set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
  {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι





theorem exists_smooth_ramp_with_turning_margin
    (P : M62.CircleProductData F circumference)
    {time : ℝ} (htime : time ∈ Icc a b)
    {e : P.charts.Point → W} (he : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → P.charts.Point}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 (n + 1)) ∞ rho U)
    (hre : ∀ p, rho (e p) = p)
    {gamma : ℝ → P.charts.Point}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hp : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma time)
    {r : ℝ} (hr : 0 < r)
    (hlength : r ≤ m62Length P.flow (fun y _ => gamma y) time)
    (hturn : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
      m63ArcLength P.flow (fun y _ => gamma y) time alpha beta ≤ r →
      m63ArcTotalCurvature P.flow (fun y _ => gamma y) time alpha beta < (1 / 200 : ℝ))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ sigma : ℝ → P.charts.Point, ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ sigma ∧
      Function.Periodic sigma curvePeriod ∧ M63IsRampAt P sigma time ∧
      (∀ x, ‖(e ∘ sigma) x - (e ∘ gamma) x‖ < epsilon ∧
        ‖deriv (e ∘ sigma) x - deriv (e ∘ gamma) x‖ < epsilon ∧
        ‖deriv (deriv (e ∘ sigma)) x - deriv (deriv (e ∘ gamma)) x‖ < epsilon) ∧
      |m62Length P.flow (fun y _ => sigma y) time -
        m62Length P.flow (fun y _ => gamma y) time| < epsilon ∧
      r / 2 < m62Length P.flow (fun y _ => sigma y) time ∧
      ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
        m63ArcLength P.flow (fun y _ => sigma y) time alpha beta ≤ r / 2 →
        m63ArcTotalCurvature P.flow (fun y _ => sigma y) time alpha beta < (3 / 400 : ℝ) := by
  let tolerance := min epsilon (min (r / 4) (1 / 400))
  have htolerance : 0 < tolerance := lt_min hepsilon (lt_min (by positivity) (by norm_num))
  have htolr : tolerance ≤ r / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have htold : tolerance ≤ (1 / 400 : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨sigma, hsigma, hsper, hsramp, hnear, harcs⟩ :=
    exists_smooth_ramp_subarc_approximation P htime he hU heU hrho hre
      hgamma hp hramp htolerance
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hfull : |m62Length P.flow (fun y _ => sigma y) time -
      m62Length P.flow (fun y _ => gamma y) time| < tolerance :=
    (harcs 0 curvePeriod hperiod (by simp)).1
  refine ⟨sigma, hsigma, hsper, hsramp, ?_, hfull.trans_le (min_le_left _ _), ?_, ?_⟩
  · intro x
    exact ⟨(hnear x).1.trans_le (min_le_left _ _),
      (hnear x).2.1.trans_le (min_le_left _ _),
      (hnear x).2.2.trans_le (min_le_left _ _)⟩
  · have hbound := (abs_lt.mp (hfull.trans_le htolr)).1
    linarith
  · intro alpha beta hab hperiodic hshort
    have herrors := harcs alpha beta hab hperiodic
    have hlength_error := (abs_lt.mp (herrors.1.trans_le htolr)).1
    have hsource : m63ArcLength P.flow (fun y _ => gamma y) time alpha beta ≤ r := by
      linarith
    have hturn_source := hturn alpha beta hab hperiodic hsource
    have hturn_error := (abs_lt.mp (herrors.2.trans_le htold)).2
    linarith

end PoincareConjecture.M64.RampTransport
