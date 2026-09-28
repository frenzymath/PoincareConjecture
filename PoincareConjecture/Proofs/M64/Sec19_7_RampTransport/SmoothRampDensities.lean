import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.RampJetDomain
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.CurveJetDensities
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.PeriodicJetTolerance
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.RampInitialBounds













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





theorem exists_smooth_ramp_density_approximation
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
      (∀ x, |curveSpeed P.flow (fun y _ => sigma y) time x -
        curveSpeed P.flow (fun y _ => gamma y) time x| < epsilon) ∧
      ∀ x, |m62Curvature P.flow (fun y _ => sigma y) time x *
          curveSpeed P.flow (fun y _ => sigma y) time x -
        m62Curvature P.flow (fun y _ => gamma y) time x *
          curveSpeed P.flow (fun y _ => gamma y) time x| < epsilon := by
  obtain ⟨hO, speed, density, hspeed, hdensity, hactual⟩ :=
    exists_continuous_curve_jet_densities P.flow he hU heU hrho hre htime
  have himm := M63.ramp_immersed P hramp
  have hc : ContDiff ℝ 2 (e ∘ gamma) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hgamma).contDiff
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hjet := fun x => (hactual gamma hgamma himm x).1
  obtain ⟨deltaSpeed, hdeltaSpeed, hspeedNear⟩ :=
    exists_periodic_jet_scalar_tolerance hO hspeed hperiod hc (hp.comp e) hjet hepsilon
  obtain ⟨deltaDensity, hdeltaDensity, hdensityNear⟩ :=
    exists_periodic_jet_scalar_tolerance hO hdensity hperiod hc (hp.comp e) hjet hepsilon
  let tolerance := min epsilon (min deltaSpeed deltaDensity)
  have htolerance : 0 < tolerance := lt_min hepsilon (lt_min hdeltaSpeed hdeltaDensity)
  have htols : tolerance ≤ deltaSpeed :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htold : tolerance ≤ deltaDensity :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨sigma, hsigma, hsper, hsramp, hnear⟩ :=
    exists_periodic_smooth_ramp_approximation P time he hU heU hrho hre
      hgamma hp hramp htolerance
  have hs2 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 sigma :=
    hsigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsimm := M63.ramp_immersed P hsramp
  have hsnear := hspeedNear (e ∘ sigma) (fun x =>
    ⟨(hnear x).1.trans_le htols, (hnear x).2.1.trans_le htols,
      (hnear x).2.2.trans_le htols⟩)
  have hdnear := hdensityNear (e ∘ sigma) (fun x =>
    ⟨(hnear x).1.trans_le htold, (hnear x).2.1.trans_le htold,
      (hnear x).2.2.trans_le htold⟩)
  refine ⟨sigma, hsigma, hsper, hsramp, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(hnear x).1.trans_le (min_le_left _ _),
      (hnear x).2.1.trans_le (min_le_left _ _),
      (hnear x).2.2.trans_le (min_le_left _ _)⟩
  · intro x
    simpa only [(hactual sigma hs2 hsimm x).2.1,
      (hactual gamma hgamma himm x).2.1] using hsnear x
  · intro x
    simpa only [(hactual sigma hs2 hsimm x).2.2,
      (hactual gamma hgamma himm x).2.2] using hdnear x

end PoincareConjecture.M64.RampTransport
