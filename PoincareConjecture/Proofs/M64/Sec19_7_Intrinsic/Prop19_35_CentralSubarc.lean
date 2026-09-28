import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubarcLengthDecrease












noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture





theorem m64Intrinsic_exists_central_boundary_subarc
    (N : IntrinsicAnnulus) {radius a b epsilon : ℝ} (hradius : radius ≠ 0)
    (hab : a < b) (hepsilon : 0 < epsilon)
    (hbudget : 2 * epsilon < intrinsicBoundaryLength N.metric radius a b) :
    ∃ p q : ℝ, a < p ∧ p < q ∧ q < b ∧
      intrinsicBoundaryLength N.metric radius a p = epsilon ∧
      intrinsicBoundaryLength N.metric radius q b = epsilon ∧
      ∀ z ∈ Icc p q,
        epsilon ≤ intrinsicBoundaryLength N.metric radius a z ∧
        epsilon ≤ intrinsicBoundaryLength N.metric radius z b := by
  let f := intrinsicBoundarySpeed N.metric radius
  let F : ℝ → ℝ := fun t => ∫ x in a..t, f x
  have hf : Continuous f := (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous
  have hFderiv (t : ℝ) : HasDerivAt F (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hFderiv t).continuousAt)
  have hFmono : StrictMono F := strictMono_of_deriv_pos fun t => by
    rw [(hFderiv t).deriv]
    exact m64Intrinsic_boundarySpeed_pos N hradius t
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hFb : F b = intrinsicBoundaryLength N.metric radius a b := rfl
  have hpExists : ∃ p ∈ Icc a b, F p = epsilon := by
    apply intermediate_value_Icc hab.le hFcont.continuousOn
    constructor
    · rw [hFa]
      exact hepsilon.le
    · rw [hFb]
      linarith
  have hqExists : ∃ q ∈ Icc a b,
      F q = intrinsicBoundaryLength N.metric radius a b - epsilon := by
    apply intermediate_value_Icc hab.le hFcont.continuousOn
    constructor
    · rw [hFa]
      linarith
    · rw [hFb]
      linarith
  obtain ⟨p, hp, hpF⟩ := hpExists
  obtain ⟨q, hq, hqF⟩ := hqExists
  have hap : a < p := by
    apply hFmono.lt_iff_lt.mp
    rw [hFa, hpF]
    exact hepsilon
  have hqb : q < b := by
    apply hFmono.lt_iff_lt.mp
    rw [hqF, hFb]
    linarith
  have hpq : p < q := by
    apply hFmono.lt_iff_lt.mp
    rw [hpF, hqF]
    linarith
  have hpLength : intrinsicBoundaryLength N.metric radius a p = epsilon := by
    exact hpF
  have hqadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a q) (hf.intervalIntegrable q b)
  have hqLength : intrinsicBoundaryLength N.metric radius q b = epsilon := by
    change F q + intrinsicBoundaryLength N.metric radius q b = F b at hqadd
    linarith
  refine ⟨p, q, hap, hpq, hqb, hpLength, hqLength, ?_⟩
  intro z hz
  have hpz : F p ≤ F z := hFmono.monotone hz.1
  have hprefix : epsilon ≤ intrinsicBoundaryLength N.metric radius a z := by
    change epsilon ≤ F z
    linarith
  have hzq : F z ≤ F q := hFmono.monotone hz.2
  have hzadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a z) (hf.intervalIntegrable z b)
  have hsuffix : epsilon ≤ intrinsicBoundaryLength N.metric radius z b := by
    change F z + intrinsicBoundaryLength N.metric radius z b = F b at hzadd
    linarith
  exact ⟨hprefix, hsuffix⟩

end PoincareConjecture
