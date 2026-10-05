import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Periodic.SmoothApproximation
import PoincareLib.Geometry.RicciFlow.Product.Circle.Identities
import PoincareLib.Geometry.CurveShortening.Ramp.Data

/-!
# Positive ramp slope as an open observed jet condition

The actual metric pairing with the fixed circle field is continuous in
the observed value and velocity. Its positive locus therefore persists
under the genuine periodic C2 approximation. No embedded boundary
hypothesis is introduced. Source: MT2007 Definition 19.12 and Lemma
19.31, pp. 446 and 464-466; M64 ramp transport approximation derivation.

Morgan--Tian context: the annulus in Lemma 19.31, printed pp. 464-466, and its intrinsic
comparison in Proposition 19.35, printed pp. 467-478.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT.M64.RampTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
  {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The genuine circle current reconstructed from the value and velocity
of an observed curve. Source: MT2007 Definition 19.12, p. 446. -/
noncomputable def rampJetCurrent (P : M62.CircleProductData F circumference)
    (time : ℝ) (rho : W → P.charts.Point) (z : W × W × W) : ℝ :=
  (P.flow.metric time).inner (rho z.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 (n + 1)) rho z.1 z.2.1)
    (P.charts.circleUnit (rho z.1))

/-- The actual circle current is continuous on the retraction domain,
including zero velocities. Source: MT2007 Lemma 19.31, pp. 464-466;
ramp transport derivation, positive slope and geometric densities. -/
theorem rampJetCurrent_continuousOn
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {U : Set W} (hU : IsOpen U) {rho : W → P.charts.Point}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 (n + 1)) ∞ rho U) :
    ContinuousOn (rampJetCurrent P time rho) (U ×ˢ (univ : Set (W × W))) := by
  let S := U ×ˢ (univ : Set (W × W))
  have hbase : ContinuousOn (fun z : W × W × W => rho z.1) S :=
    hrho.continuousOn.comp continuousOn_fst (fun _ hz => hz.1)
  have ht := hrho.continuousOn_tangentMapWithin (by simp) hU.uniqueMDiffOn
  have hpush0 : ContinuousOn (fun z : W × W × W =>
      (⟨rho z.1, mfderivWithin 𝓘(ℝ, W) (𝓡 (n + 1)) rho U z.1 z.2.1⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point)) S :=
    ht.comp (((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, W)).symm.continuous.comp
      (continuous_fst.prodMk continuous_snd.fst)).continuousOn) (fun _ hz => hz.1)
  have hpush : ContinuousOn (fun z : W × W × W =>
      (⟨rho z.1, mfderiv 𝓘(ℝ, W) (𝓡 (n + 1)) rho z.1 z.2.1⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point)) S := by
    apply hpush0.congr
    intro z hz
    dsimp only
    erw [mfderivWithin_of_isOpen hU hz.1]
  have hcircle := (M62.circleProduct_identities P).circle_unit_smooth.continuous.comp_continuousOn
    hbase
  have hmetric := (P.flow.metric time).contMDiff.continuous.comp_continuousOn hbase
  intro z hz
  have h := (hmetric z hz).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial P.charts.Point ℝ) (hpush z hz) (hcircle z hz)
  rw [FiberBundle.continuousWithinAt_totalSpace] at h
  exact h.2

/-- The observed circle current at an actual embedded curve is its
genuine velocity pairing. Source: MT2007 Definition 19.12, p. 446. -/
theorem rampJetCurrent_actual
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {e : P.charts.Point → W} (he : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → P.charts.Point}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 (n + 1)) ∞ rho U)
    (hre : ∀ p, rho (e p) = p)
    {gamma : ℝ → P.charts.Point}
    (hgamma : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma) (x : ℝ) :
    rampJetCurrent P time rho ((e ∘ gamma) x, deriv (e ∘ gamma) x,
      deriv (deriv (e ∘ gamma)) x) =
      (P.flow.metric time).inner (gamma x) (curveVelocity gamma x)
        (P.charts.circleUnit (gamma x)) := by
  have hleft := (M63.smooth_retraction_differentials he hU heU hrho hre).2.2
  have hd := mfderiv_comp_apply (f := gamma) (g := e) x
    (he.mdifferentiable (by simp) _) (hgamma x) 1
  rw [mfderiv_eq_fderiv] at hd
  change deriv (e ∘ gamma) x =
    mfderiv (𝓡 (n + 1)) 𝓘(ℝ, W) e (gamma x) (curveVelocity gamma x) at hd
  dsimp only [rampJetCurrent, Function.comp_apply]
  rw [hd, hleft, hre]

/-- A positive circle current is equivalent to positive actual slope.
Zero speed is excluded by the positive current itself. Source: MT2007
Definition 19.12, p. 446. -/
theorem ramp_iff_circle_current_positive
    (P : M62.CircleProductData F circumference) (time : ℝ)
    (gamma : ℝ → P.charts.Point) :
    M63IsRampAt P gamma time ↔
      ∀ x, 0 < (P.flow.metric time).inner (gamma x) (curveVelocity gamma x)
        (P.charts.circleUnit (gamma x)) := by
  constructor
  · intro hramp x
    have h := hramp x
    change 0 < (P.flow.metric time).inner (gamma x)
      ((curveSpeed P.flow (fun y _ => gamma y) time x)⁻¹ • curveVelocity gamma x)
      (P.charts.circleUnit (gamma x)) at h
    rw [map_smul, smul_apply, smul_eq_mul] at h
    exact pos_of_mul_pos_right h (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · intro hcurrent x
    have hne : curveVelocity (n := n + 1) gamma x ≠ 0 := by
      intro hz
      have h := hcurrent x
      rw [hz, map_zero] at h
      exact lt_irrefl 0 h
    have hspeed : 0 < curveSpeed P.flow (fun y _ => gamma y) time x :=
      Real.sqrt_pos.mpr ((P.flow.metric time).pos _ _ hne)
    change 0 < (P.flow.metric time).inner (gamma x)
      ((curveSpeed P.flow (fun y _ => gamma y) time x)⁻¹ • curveVelocity gamma x)
      (P.charts.circleUnit (gamma x))
    rw [map_smul, smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hspeed) (hcurrent x)

/-- The actual C2 ramp has smooth periodic ramp approximants with all
three embedded jets uniformly close. Source: MT2007 Lemma 19.31,
pp. 464-466; ramp transport derivation. -/
theorem exists_periodic_smooth_ramp_approximation
    [FiniteDimensional ℝ W]
    (P : M62.CircleProductData F circumference) (time : ℝ)
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
      ∀ x, ‖(e ∘ sigma) x - (e ∘ gamma) x‖ < epsilon ∧
        ‖deriv (e ∘ sigma) x - deriv (e ∘ gamma) x‖ < epsilon ∧
        ‖deriv (deriv (e ∘ sigma)) x - deriv (deriv (e ∘ gamma)) x‖ < epsilon := by
  let O := (U ×ˢ (univ : Set (W × W))) ∩ rampJetCurrent P time rho ⁻¹' Ioi 0
  have hO : IsOpen O := (rampJetCurrent_continuousOn P time hU hrho).isOpen_inter_preimage
    (hU.prod isOpen_univ) isOpen_Ioi
  have hcurrent := (ramp_iff_circle_current_positive P time gamma).mp hramp
  have hjet (x : ℝ) : ((e ∘ gamma) x, deriv (e ∘ gamma) x,
      deriv (deriv (e ∘ gamma)) x) ∈ O := by
    refine ⟨⟨heU (mem_range_self _), mem_univ _⟩, ?_⟩
    change 0 < rampJetCurrent P time rho _
    rw [rampJetCurrent_actual P time he hU heU hrho hre
      (hgamma.mdifferentiable (by norm_num))]
    exact hcurrent x
  obtain ⟨sigma, hsigma, hsper, hsjet, hnear⟩ :=
    exists_periodic_smooth_approximation_in_open_jets he hU heU hrho hre
      (show 0 < curvePeriod by unfold curvePeriod; positivity) hgamma hp hO hjet hepsilon
  refine ⟨sigma, hsigma, hsper, ?_, hnear⟩
  apply (ramp_iff_circle_current_positive P time sigma).mpr
  intro x
  have h := (hsjet x).2
  change 0 < rampJetCurrent P time rho _ at h
  rw [rampJetCurrent_actual P time he hU heU hrho hre
    (hsigma.mdifferentiable (by simp))] at h
  exact h

end PoincareMT.M64.RampTransport
