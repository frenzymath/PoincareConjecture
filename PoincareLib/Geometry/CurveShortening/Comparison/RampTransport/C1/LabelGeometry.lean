import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Curve.JetDensities
import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Periodic.SmoothApproximation
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Relabel.Length
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.C2.GaugeWitnesses

/-!
# Literal geometric transport through immersed C1 boundary labels

The actual labelled boundary immersion forces the monotone label's
derivative to be positive. The first-derivative connection chain rule
therefore transports curvature without upgrading the label to C2.
Source: MT2007 Lemmas 19.6 and 19.31, pp. 441 and 464-466; ramp transport
trimming derivation, literal C1 boundary labels.

Morgan--Tian context: the annulus in Lemma 19.31, printed pp. 464-466, and its intrinsic
comparison in Proposition 19.35, printed pp. 467-478.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

omit [IsManifold (𝓡 n) ∞ M] in
/-- Immersion of a monotone C1 relabeling forces a strictly positive label
derivative. Source: MT Lemma 19.31, pp. 464-466; C1 label transport derivation. -/
theorem c1_label_deriv_pos_of_immersed
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    {sigma : ℝ → ℝ} (hsigma : ContDiff ℝ 1 sigma) (hmono : Monotone sigma)
    (himm : ∀ x, curveVelocity (n := n) (gamma ∘ sigma) x ≠ 0) (x : ℝ) :
    0 < deriv sigma x := by
  have hn : deriv sigma x ≠ 0 := by
    intro hzero
    apply himm x
    have hvel := M63.curveVelocity_comp (hgamma.mdifferentiableAt (by norm_num))
      (hsigma.differentiable (by norm_num) x).hasDerivAt
    simpa +instances only [Function.comp_def, hzero, zero_smul] using! hvel
  exact lt_of_le_of_ne hmono.deriv_nonneg (Ne.symm hn)

/-- C1 labels preserve actual curvature whenever the labelled curve is immersed. Only the
original curve's normalized tangent needs C1 regularity. Source: Morgan--Tian Lemma 19.31,
printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem curvature_comp_immersed_c1
    (F : RicciFlow n M (Icc a b)) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (hgammaImm : ∀ x, curveVelocity (n := n) gamma x ≠ 0)
    {sigma : ℝ → ℝ} (hsigma : ContDiff ℝ 1 sigma) (hmono : Monotone sigma)
    (himm : ∀ x, curveVelocity (n := n) (gamma ∘ sigma) x ≠ 0) (x : ℝ) :
    m62Curvature F (fun y _ => gamma (sigma y)) time x =
      m62Curvature F (fun y _ => gamma y) time (sigma x) := by
  have hpos := c1_label_deriv_pos_of_immersed (hgamma.of_le (by norm_num)) hsigma hmono himm
  have hS := M63.unitTangent_contMDiff_of_c2 F (fun y _ => gamma y)
    (t := time) hgamma hgammaImm
  have hvec := M63.curvatureVector_comp F (fun y _ => gamma y)
    (hgamma.mdifferentiable (by norm_num)) (hsigma.differentiable (by norm_num)) hpos
      (hS.mdifferentiableAt (by norm_num) (x := sigma x))
  unfold m62Curvature m62CurvatureSquared
  rw [hvec]

/-- The actual C1 degree-one label preserves full length and transports both subarc
integrals by its literal endpoints. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466;
project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem c1_lift_subarc_geometry [T2Space M] [CompactSpace M]
    (F : RicciFlow n M (Icc a b)) {time : ℝ} (htime : time ∈ Icc a b)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (hp : Function.Periodic gamma curvePeriod)
    (hgammaImm : ∀ x, curveVelocity (n := n) gamma x ≠ 0)
    (sigma : M64PeriodicDegreeOneLift) (hsigma : ContDiff ℝ 1 sigma.map)
    (himm : ∀ x, curveVelocity (n := n) (gamma ∘ sigma.map) x ≠ 0) :
    m62Length F (fun y _ => gamma (sigma.map y)) time =
        m62Length F (fun y _ => gamma y) time ∧
      ∀ alpha beta : ℝ,
        m63ArcLength F (fun y _ => gamma (sigma.map y)) time alpha beta =
          m63ArcLength F (fun y _ => gamma y) time (sigma.map alpha) (sigma.map beta) ∧
        m63ArcTotalCurvature F (fun y _ => gamma (sigma.map y)) time alpha beta =
          m63ArcTotalCurvature F (fun y _ => gamma y) time (sigma.map alpha) (sigma.map beta) := by
  let : Nonempty M := ⟨gamma 0⟩
  obtain ⟨dimension, e, he, hemb, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, rho, hU, heU, hrho, hre, _hmin, _huniq⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  have hcont := actual_curve_densities_continuous F he hU heU hrho hre htime hgamma hgammaImm
  have hdiff := hgamma.mdifferentiable (by norm_num)
  refine ⟨length_comp_lift F (fun y _ => gamma y) (hgamma.of_le (by norm_num))
    hp sigma hsigma, ?_⟩
  intro alpha beta
  refine ⟨arcLength_comp_monotone F (fun y _ => gamma y) hdiff hcont.1 hsigma
    sigma.monotone alpha beta, ?_⟩
  unfold m63ArcTotalCurvature
  calc
    _ = ∫ x in alpha..beta, m62Curvature F (fun y _ => gamma y) time (sigma.map x) *
        curveSpeed F (fun y _ => gamma (sigma.map y)) time x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only
      rw [curvature_comp_immersed_c1 F time hgamma hgammaImm hsigma sigma.monotone himm x]
    _ = _ := integral_density_comp_monotone F (fun y _ => gamma y) hdiff hsigma
      sigma.monotone (m62Curvature F (fun y _ => gamma y) time) hcont.2 alpha beta

/-- Monotonicity and degree one preserve the source small-subarc turning condition after
literal C1 relabeling. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466; project
derivation `proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem c1_lift_turning_bound [T2Space M] [CompactSpace M]
    (F : RicciFlow n M (Icc a b)) {time : ℝ} (htime : time ∈ Icc a b)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (hp : Function.Periodic gamma curvePeriod)
    (hgammaImm : ∀ x, curveVelocity (n := n) gamma x ≠ 0)
    (sigma : M64PeriodicDegreeOneLift) (hsigma : ContDiff ℝ 1 sigma.map)
    (himm : ∀ x, curveVelocity (n := n) (gamma ∘ sigma.map) x ≠ 0)
    {r delta : ℝ}
    (hturn : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
      m63ArcLength F (fun y _ => gamma y) time alpha beta ≤ r →
      m63ArcTotalCurvature F (fun y _ => gamma y) time alpha beta < delta) :
    ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
      m63ArcLength F (fun y _ => gamma (sigma.map y)) time alpha beta ≤ r →
      m63ArcTotalCurvature F (fun y _ => gamma (sigma.map y)) time alpha beta < delta := by
  have hgeom := (c1_lift_subarc_geometry F htime hgamma hp hgammaImm sigma hsigma himm).2
  intro alpha beta hab hper hshort
  rw [(hgeom alpha beta).1] at hshort
  rw [(hgeom alpha beta).2]
  apply hturn (sigma.map alpha) (sigma.map beta) (sigma.monotone hab) _ hshort
  simpa only [sigma.period_shift] using sigma.monotone hper

end PoincareMT.M64.RampTransport
