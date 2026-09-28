import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.SmoothRampArcs

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}
  {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι

theorem exists_immersed_curve_density_tolerance
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U) (hre : ∀ p, rho (e p) = p)
    {time : ℝ} (htime : time ∈ Icc a b)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (hp : Function.Periodic gamma curvePeriod)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ sigma : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 sigma →
      (∀ x, ‖(e ∘ sigma) x - (e ∘ gamma) x‖ < delta ∧
        ‖deriv (e ∘ sigma) x - deriv (e ∘ gamma) x‖ < delta ∧
        ‖deriv (deriv (e ∘ sigma)) x - deriv (deriv (e ∘ gamma)) x‖ < delta) →
      (∀ x, curveVelocity (n := n) sigma x ≠ 0) ∧
      (∀ x, |curveSpeed F (fun y _ => sigma y) time x -
        curveSpeed F (fun y _ => gamma y) time x| < epsilon) ∧
      ∀ x, |m62Curvature F (fun y _ => sigma y) time x *
          curveSpeed F (fun y _ => sigma y) time x -
        m62Curvature F (fun y _ => gamma y) time x *
          curveSpeed F (fun y _ => gamma y) time x| < epsilon := by
  obtain ⟨hO, speed, density, hspeed, hdensity, hactual⟩ :=
    exists_continuous_curve_jet_densities F he hU heU hrho hre htime
  let c := e ∘ gamma
  have hc : ContDiff ℝ 2 c :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hgamma).contDiff
  have hc1 : ContDiff ℝ 1 (deriv c) := hc.deriv' (n := 1)
  have hcp : Function.Periodic c curvePeriod := hp.comp e
  have hp1 := hcp.deriv_of_differentiable (hc.differentiable (by norm_num))
  have hp2 := hp1.deriv_of_differentiable (hc1.differentiable (by norm_num))
  let jet := fun x => (c x, deriv c x, deriv (deriv c) x)
  have hjetp : Function.Periodic jet curvePeriod := by
    intro x
    simp only [jet, hcp x, hp1 x, hp2 x]
  have hjetc : Continuous jet :=
    hc.continuous.prodMk (hc1.continuous.prodMk hc1.continuous_deriv_one)
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hcompact : IsCompact (range jet) :=
    hjetp.compact_of_continuous hperiod.ne' hjetc
  obtain ⟨eta, heta, hthick⟩ := hcompact.exists_thickening_subset_open hO (by
    rintro _ ⟨x, rfl⟩
    exact (hactual gamma hgamma himm x).1)
  obtain ⟨ds, hds, hsnear⟩ := exists_periodic_jet_scalar_tolerance hO hspeed
    hperiod hc hcp (fun x => (hactual gamma hgamma himm x).1) hepsilon
  obtain ⟨dk, hdk, hknear⟩ := exists_periodic_jet_scalar_tolerance hO hdensity
    hperiod hc hcp (fun x => (hactual gamma hgamma himm x).1) hepsilon
  let delta := min eta (min ds dk)
  refine ⟨delta, lt_min heta (lt_min hds hdk), ?_⟩
  intro sigma hsigma hnear
  have htargetImm (x : ℝ) : curveVelocity (n := n) sigma x ≠ 0 := by
    have hmem : ((e ∘ sigma) x, deriv (e ∘ sigma) x,
        deriv (deriv (e ∘ sigma)) x) ∈
        {z : W × W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1 z.2.1 ≠ 0} := by
      apply hthick
      apply Metric.mem_thickening_iff.mpr
      refine ⟨jet x, mem_range_self x, ?_⟩
      rw [dist_eq_norm]
      exact (max_lt (hnear x).1 (max_lt (hnear x).2.1 (hnear x).2.2)).trans_le
        (min_le_left _ _)
    have hvel := observed_velocity_reconstruction he hU heU hrho hre
      (hsigma.mdifferentiable (by norm_num)) x
    exact hvel ▸ hmem.2
  have hs := hsnear (e ∘ sigma) (fun x =>
    ⟨(hnear x).1.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      (hnear x).2.1.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      (hnear x).2.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩)
  have hk := hknear (e ∘ sigma) (fun x =>
    ⟨(hnear x).1.trans_le ((min_le_right _ _).trans (min_le_right _ _)),
      (hnear x).2.1.trans_le ((min_le_right _ _).trans (min_le_right _ _)),
      (hnear x).2.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩)
  refine ⟨htargetImm, ?_, ?_⟩
  · intro x
    simpa only [c, (hactual sigma hsigma htargetImm x).2.1,
      (hactual gamma hgamma himm x).2.1] using hs x
  · intro x
    simpa only [c, (hactual sigma hsigma htargetImm x).2.2,
      (hactual gamma hgamma himm x).2.2] using hk x

theorem exists_immersed_curve_subarc_tolerance
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U) (hre : ∀ p, rho (e p) = p)
    {time : ℝ} (htime : time ∈ Icc a b)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (hp : Function.Periodic gamma curvePeriod)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ sigma : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 sigma →
      (∀ x, ‖(e ∘ sigma) x - (e ∘ gamma) x‖ < delta ∧
        ‖deriv (e ∘ sigma) x - deriv (e ∘ gamma) x‖ < delta ∧
        ‖deriv (deriv (e ∘ sigma)) x - deriv (deriv (e ∘ gamma)) x‖ < delta) →
      (∀ x, curveVelocity (n := n) sigma x ≠ 0) ∧
      ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
        |m63ArcLength F (fun y _ => sigma y) time alpha beta -
          m63ArcLength F (fun y _ => gamma y) time alpha beta| < epsilon ∧
        |m63ArcTotalCurvature F (fun y _ => sigma y) time alpha beta -
          m63ArcTotalCurvature F (fun y _ => gamma y) time alpha beta| < epsilon := by
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  obtain ⟨delta, hdelta, hnear⟩ := exists_immersed_curve_density_tolerance F he hU heU hrho hre
    htime hgamma hp himm (show 0 < epsilon / (2 * curvePeriod) by positivity)
  refine ⟨delta, hdelta, ?_⟩
  intro sigma hsigma hclose
  obtain ⟨hsimm, hspeed, hturn⟩ := hnear sigma hsigma hclose
  have hc := actual_curve_densities_continuous F he hU heU hrho hre htime hgamma himm
  have hs := actual_curve_densities_continuous F he hU heU hrho hre htime hsigma hsimm
  refine ⟨hsimm, ?_⟩
  intro alpha beta hab hlength
  exact ⟨subarc_integral_error_of_uniform_density hs.1 hc.1 hperiod hepsilon hspeed hab hlength,
    subarc_integral_error_of_uniform_density hs.2 hc.2 hperiod hepsilon hturn hab hlength⟩

end PoincareConjecture.M64.RampTransport
