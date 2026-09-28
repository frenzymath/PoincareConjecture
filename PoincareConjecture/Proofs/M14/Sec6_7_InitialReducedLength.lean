import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialCoherence
import PoincareConjecture.Proofs.M14.Sec6_1_SquareDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

private theorem tendsto_intervalAverage_right {b : ℝ} (hb : 0 < b)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 b)) :
    Tendsto (fun r => (∫ t in 0..r, f t) / r) (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
  let : Fact ((0 : ℝ) ∈ Icc 0 b) := ⟨⟨le_rfl, hb.le⟩⟩
  have hi : IntervalIntegrable f volume 0 0 := by simp
  have hd := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc 0 b) (t := Icc 0 b) hi
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc 0) (hf 0 ⟨le_rfl, hb.le⟩)
  have hl := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Icc_sdiff_left, nhdsWithin_Ioc_eq_nhdsGT hb] at hl
  change Tendsto (fun r => slope (fun u => ∫ t in 0..u, f t) 0 r)
    (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) at hl
  simpa only [slope_def_field, intervalIntegral.integral_same, sub_zero] using hl

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem initial_inner_transport {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) :
    G.spacetime.horizontalMetric.inner q v v =
      G.spacetime.horizontalMetric.inner r (h ▸ v) (h ▸ v) := by
  cases h
  rfl

theorem exponential_squareDensity_zero
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {b : ℝ}
    (hb : (Z, b) ∈ E.domain) (hpos : 0 < b) :
    squareRootLIntegrand (E.square_path Z b hb hpos) 0 / 2 =
      G.spacetime.horizontalMetric.inner x Z Z := by
  obtain ⟨hpoint, hA⟩ := E.square_initial_velocity Z b hb hpos
  have hinner := initial_inner_transport hpoint ((E.square_path Z b hb hpos).horizontal_velocity 0)
  rw [hA] at hinner
  simp only [map_smul, smul_apply, smul_eq_mul] at hinner
  simp only [squareRootLIntegrand, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
    zero_add, hinner]
  ring

theorem tendsto_exponential_reducedLength_zero
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {b : ℝ}
    (hb : (Z, b) ∈ E.domain) (hpos : 0 < b) :
    Tendsto (E.reduced_length Z) (𝓝[>] (0 : ℝ))
      (𝓝 (G.spacetime.horizontalMetric.inner x Z Z)) := by
  let P := exponentialInitialValuePath E Z b hb hpos
  have hc : ContinuousOn (squareRootLIntegrand P.square_path) (Icc 0 b) := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
      (squareRootLIntegrand_contDiffOn hM12 P.square_path).continuousOn
  have hl :=
    (tendsto_intervalAverage_right hpos (squareRootLIntegrand P.square_path) hc).div_const 2
  have hvalue : squareRootLIntegrand P.square_path 0 / 2 =
      G.spacetime.horizontalMetric.inner x Z Z := exponential_squareDensity_zero E hb hpos
  rw [hvalue] at hl
  have heq : E.reduced_length Z =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r => (∫ t in 0..r, squareRootLIntegrand P.square_path t) / r / 2) := by
    filter_upwards [Ioc_mem_nhdsGT hpos] with r hr
    have hsurv := (E.maximal_lifetime Z).out (E.domain_zero Z) hb ⟨hr.1.le, hr.2⟩
    rw [E.reduced_length_eq Z r hsurv hr.1,
      exponentialFamily_action_eq hM04 hM12 E hsurv hr.1,
      initialValueAction_eq_integral_prefix hM04 hM12 P
        (by simpa only [Real.sqrt_sq hpos.le] using ⟨hr.1.le, hr.2⟩)]
    ring
  exact hl.congr' heq.symm

end PoincareConjecture.M14
