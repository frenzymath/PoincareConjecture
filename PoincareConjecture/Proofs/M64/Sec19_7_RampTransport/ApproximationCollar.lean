import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.ObservedMetricTolerance
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.CurveJetDensities
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.PeriodicJetTolerance
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ShortBoundaryCollar

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι

theorem exists_c2_approximation_collar_tolerance
    (F : RicciFlow n M (Icc a b))
    {time : ℝ} (htime : time ∈ Icc a b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U) (hre : ∀ p, rho (e p) = p)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (hp : Function.Periodic gamma curvePeriod)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ sigma : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 sigma → Function.Periodic sigma curvePeriod →
      (∀ x, curveVelocity (n := n) sigma x ≠ 0) →
      (∀ x, ‖(e ∘ sigma) x - (e ∘ gamma) x‖ < delta ∧
        ‖deriv (e ∘ sigma) x - deriv (e ∘ gamma) x‖ < delta ∧
        ‖deriv (deriv (e ∘ sigma)) x - deriv (deriv (e ∘ gamma)) x‖ < delta) →
      ∃ A : M64Annulus (F.metric time) gamma sigma, A.area < epsilon := by
  obtain ⟨hO, speed, _density, hspeed, _hdensity, hactual⟩ :=
    exists_continuous_curve_jet_densities F he hU heU hrho hre htime
  have hsource := actual_curve_densities_continuous F he hU heU hrho hre htime hgamma himm
  obtain ⟨S, hS⟩ := isCompact_Icc.bddAbove_image
    (hsource.1.continuousOn : ContinuousOn (curveSpeed F (fun y _ => gamma y) time)
      (Icc (0 : ℝ) curvePeriod))
  obtain ⟨radius, hradius, C, hC, hcollar⟩ :=
    exists_short_boundary_collar (F.metric time) isCompact_univ (S + 1)
  let displacement := min radius (epsilon / (2 * C))
  have hdisplacement : 0 < displacement := lt_min hradius (by positivity)
  obtain ⟨deltaMetric, hdeltaMetric, hmetric⟩ :=
    exists_observed_metric_tolerance (F.metric time) he hU heU hrho hre hdisplacement
  have hc : ContDiff ℝ 2 (e ∘ gamma) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hgamma).contDiff
  have hperiod : 0 < curvePeriod := by unfold curvePeriod; positivity
  obtain ⟨deltaSpeed, hdeltaSpeed, hspeedNear⟩ :=
    exists_periodic_jet_scalar_tolerance hO hspeed hperiod hc (hp.comp e)
      (fun x => (hactual gamma hgamma himm x).1) (show (0 : ℝ) < 1 by norm_num)
  let delta := min deltaMetric deltaSpeed
  refine ⟨delta, lt_min hdeltaMetric hdeltaSpeed, ?_⟩
  intro sigma hsigma hsper hsimm hnear
  have hsn := hspeedNear (e ∘ sigma) (fun x =>
    ⟨(hnear x).1.trans_le (min_le_right _ _), (hnear x).2.1.trans_le (min_le_right _ _),
      (hnear x).2.2.trans_le (min_le_right _ _)⟩)
  have hsnear (x : ℝ) : |curveSpeed F (fun y _ => sigma y) time x -
      curveSpeed F (fun y _ => gamma y) time x| < 1 := by
    simpa only [(hactual sigma hsigma hsimm x).2.1,
      (hactual gamma hgamma himm x).2.1] using hsn x
  have hsourceSpeed (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      (F.metric time).tangentNorm (gamma x) (curveVelocity gamma x) ≤ S + 1 := by
    have h := hS (mem_image_of_mem (curveSpeed F (fun y _ => gamma y) time) hx)
    change curveSpeed F (fun y _ => gamma y) time x ≤ S + 1
    linarith
  have htargetSpeed (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      (F.metric time).tangentNorm (sigma x) (curveVelocity sigma x) ≤ S + 1 := by
    have h := hS (mem_image_of_mem (curveSpeed F (fun y _ => gamma y) time) hx)
    have hdiff := (abs_lt.mp (hsnear x)).2
    change curveSpeed F (fun y _ => sigma y) time x ≤ S + 1
    linarith
  have hclose (x : ℝ) : (F.metric time).edist (gamma x) (sigma x) ≤
      ENNReal.ofReal displacement := by
    apply (hmetric (gamma x) (sigma x) ?_).le
    rw [norm_sub_rev]
    exact (hnear x).1.trans_le (min_le_left _ _)
  obtain ⟨A, hA⟩ := hcollar gamma sigma (hgamma.of_le (by norm_num))
    (hsigma.of_le (by norm_num)) hp hsper hsourceSpeed htargetSpeed displacement
    hdisplacement.le (min_le_left _ _) hclose
  refine ⟨A, hA.trans_lt ?_⟩
  calc
    C * displacement ≤ C * (epsilon / (2 * C)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
    _ = epsilon / 2 := by field_simp
    _ < epsilon := half_lt_self hepsilon

end PoincareConjecture.M64.RampTransport
