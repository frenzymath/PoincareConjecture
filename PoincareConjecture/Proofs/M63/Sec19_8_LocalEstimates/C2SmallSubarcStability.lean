import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.C2ScalarRegularity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.LocalCurveTheory
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem c2_smallSubarcs_eventually [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (c : ℝ → ℝ → M) (hc : M63C2ShrinkingCurveOn F c (Icc a b))
    {s r r' delta delta' : ℝ} (hs : s ∈ Icc a b)
    (hRadius : r' < r) (hTolerance : delta < delta')
    (hSmall : M63SmallSubarcs F c s r delta) :
    ∀ᶠ t in 𝓝[Icc a b] s, M63SmallSubarcs F c t r' delta' := by
  have hab : a < b := by
    obtain ⟨u, hu, v, hv, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith only [hu.1, hu.2, hv.1, hv.2, h]
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hlocal := localCurveTheory_of_compact F hcompact
  have hv := c2_speed_continuousOn F c hc hab
  have hvper (t : ℝ) (ht : t ∈ Icc a b) := c2_speed_periodic F c hc ht
  let density : ℝ → ℝ → ℝ := fun t x => m62Curvature F c t x * curveSpeed F c t x
  have hdensity : ContinuousOn (fun z : ℝ × ℝ => density z.2 z.1)
      (univ ×ˢ Icc a b) := (c2_curvature_continuousOn F c hc hab).mul hv
  have hdensityper (t : ℝ) (ht : t ∈ Icc a b) :
      Function.Periodic (density t) curvePeriod := by
    intro x
    dsimp only [density, m62Curvature]
    rw [c2_curvatureSquared_periodic F c hc hlocal hab ht x, hvper t ht x]
  have harc (f : ℝ → ℝ → ℝ)
      (hcont : ContinuousOn (fun z : ℝ × ℝ => f z.2 z.1) (univ ×ˢ Icc a b))
      (hperiod : ∀ t ∈ Icc a b, Function.Periodic (f t) curvePeriod)
      {epsilon : ℝ} (hepsilon : 0 < epsilon) :
      ∀ᶠ t in 𝓝[Icc a b] s, ∀ alpha beta : ℝ,
        alpha ≤ beta → beta ≤ alpha + curvePeriod →
        |(∫ x in alpha..beta, f t x) - (∫ x in alpha..beta, f s x)| ≤
          epsilon * curvePeriod := by
    have hcompactStrip : IsCompact (Icc (0 : ℝ) (2 * curvePeriod)) := isCompact_Icc
    have hswap : ContinuousOn f.uncurry (Icc a b ×ˢ Icc 0 (2 * curvePeriod)) :=
      hcont.comp continuous_swap.continuousOn (fun _ hz => ⟨mem_univ _, hz.1⟩)
    obtain ⟨U, hU, huniform⟩ : ∃ U ∈ 𝓝[Icc a b] s,
        ∀ t ∈ U, ∀ x ∈ Icc 0 (2 * curvePeriod), dist (f t x) (f s x) < epsilon :=
      hcompactStrip.mem_uniformity_of_prod hswap hs (Metric.dist_mem_uniformity hepsilon)
    have hslice (t : ℝ) (ht : t ∈ Icc a b) : Continuous (f t) :=
      hcont.comp_continuous (continuous_id.prodMk continuous_const)
        (fun _ => ⟨mem_univ _, ht⟩)
    filter_upwards [hU, self_mem_nhdsWithin] with t htU ht
    intro alpha beta horder hone
    let k := toIcoDiv hP 0 alpha
    let d : ℝ := (k : ℝ) * curvePeriod
    have hnormal : alpha - d ∈ Ico 0 curvePeriod := by
      dsimp only [d, k]
      simpa only [zero_add, zsmul_eq_mul] using sub_toIcoDiv_zsmul_mem_Ico hP 0 alpha
    have horder' : alpha - d ≤ beta - d := sub_le_sub_right horder d
    have hstrip (x : ℝ) (hx : x ∈ Icc (alpha - d) (beta - d)) :
        x ∈ Icc 0 (2 * curvePeriod) := by
      constructor <;> linarith only [hnormal.1, hnormal.2, hone, hx.1, hx.2]
    have hshift (u : ℝ) (hu : u ∈ Icc a b) :
        (∫ x in alpha..beta, f u x) = ∫ x in alpha - d..beta - d, f u x := by
      calc
        _ = ∫ x in alpha..beta, f u (x - d) := by
          apply intervalIntegral.integral_congr
          intro x _
          exact ((hperiod u hu).sub_int_mul_eq k).symm
        _ = _ := intervalIntegral.integral_comp_sub_right (f := f u) d
    have hIt : IntervalIntegrable (f t) volume (alpha - d) (beta - d) :=
      (hslice t ht).intervalIntegrable _ _
    have hIs : IntervalIntegrable (f s) volume (alpha - d) (beta - d) :=
      (hslice s hs).intervalIntegrable _ _
    rw [hshift t ht, hshift s hs, ← intervalIntegral.integral_sub hIt hIs]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := alpha - d) (b := beta - d) (f := fun x => f t x - f s x)
      (C := epsilon) (by
        intro x hx
        have hx' : x ∈ Icc (alpha - d) (beta - d) :=
          Ioc_subset_Icc_self (by simpa only [uIoc_of_le horder'] using hx)
        simpa only [Real.norm_eq_abs, Real.dist_eq] using
          (huniform t htU x (hstrip x hx')).le)
    have hlength : |(beta - d) - (alpha - d)| ≤ curvePeriod := by
      rw [abs_of_nonneg (sub_nonneg.mpr horder')]
      linarith only [hone]
    exact (show |∫ x in alpha - d..beta - d, f t x - f s x| ≤
      epsilon * |(beta - d) - (alpha - d)| by
        simpa only [Real.norm_eq_abs] using hbound).trans
          (mul_le_mul_of_nonneg_left hlength hepsilon.le)
  let epsilonL := (r - r') / (2 * curvePeriod)
  let epsilonD := (delta' - delta) / (2 * curvePeriod)
  have hepsilonL : 0 < epsilonL :=
    div_pos (sub_pos.mpr hRadius) (mul_pos (by norm_num) hP)
  have hepsilonD : 0 < epsilonD :=
    div_pos (sub_pos.mpr hTolerance) (mul_pos (by norm_num) hP)
  have hmarginL : epsilonL * (2 * curvePeriod) = r - r' :=
    div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hP.ne')
  have hmarginD : epsilonD * (2 * curvePeriod) = delta' - delta :=
    div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hP.ne')
  filter_upwards [harc (curveSpeed F c) hv hvper hepsilonL,
    harc density hdensity hdensityper hepsilonD] with t htL htD
  intro alpha beta horder hone hlength
  have hL := (abs_le.mp (htL alpha beta horder hone)).1
  change -(epsilonL * curvePeriod) ≤
    m63ArcLength F c t alpha beta - m63ArcLength F c s alpha beta at hL
  have hinitial : m63ArcLength F c s alpha beta ≤ r := by
    nlinarith only [hL, hlength, hmarginL, hRadius]
  have hturn := hSmall alpha beta horder hone hinitial
  have hD := (abs_le.mp (htD alpha beta horder hone)).2
  change m63ArcTotalCurvature F c t alpha beta - m63ArcTotalCurvature F c s alpha beta ≤
    epsilonD * curvePeriod at hD
  nlinarith only [hD, hturn, hmarginD, hTolerance]

end PoincareConjecture.M63
