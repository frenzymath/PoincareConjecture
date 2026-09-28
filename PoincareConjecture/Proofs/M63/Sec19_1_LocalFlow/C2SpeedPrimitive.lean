import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2NormalizationContinuity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2IntrinsicSpeedEvolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem c2ShrinkingCurve_speed_eq_exp_integral
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M} {J : Set ℝ}
    (hc : M63C2ShrinkingCurveOn F c J)
    (hH : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × ℝ => (⟨c z.1 z.2, m62CurvatureVector F c z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ interior J))
    {s t : ℝ} (hst : s ≤ t) (hsub : Icc s t ⊆ J) (x : ℝ) :
    curveSpeed F c t x = curveSpeed F c s x *
      Real.exp (-(∫ r in s..t, m62TangentRicci F c r x +
        m62CurvatureSquared F c r x)) := by
  obtain ⟨hv, hA⟩ := c2ShrinkingCurve_speed_normalization_continuousOn F hc
  have hmaps : MapsTo (fun r : ℝ => (x, r)) (Icc s t) (univ ×ˢ J) :=
    fun _ hr => ⟨mem_univ _, hsub hr⟩
  have hvcont : ContinuousOn (fun r => curveSpeed F c r x) (Icc s t) :=
    hv.comp (s := Icc s t) (f := fun r : ℝ => (x, r))
      (continuous_const.prodMk continuous_id).continuousOn hmaps
  have hAcont : ContinuousOn
      (fun r => m62TangentRicci F c r x + m62CurvatureSquared F c r x) (Icc s t) :=
    hA.comp (s := Icc s t) (f := fun r : ℝ => (x, r))
      (continuous_const.prodMk continuous_id).continuousOn hmaps
  have hpos (r : ℝ) (hr : r ∈ Icc s t) : 0 < curveSpeed F c r x :=
    Real.sqrt_pos.mpr ((F.metric r).pos _ _ (hc.immersed r (hsub hr) x))
  have hlog := hvcont.log (fun r hr => (hpos r hr).ne')
  have hio : Ioo s t ⊆ interior J :=
    isOpen_Ioo.subset_interior_iff.mpr (Ioo_subset_Icc_self.trans hsub)
  have hderiv (r : ℝ) (hr : r ∈ Ioo s t) :
      HasDerivAt (fun u => Real.log (curveSpeed F c u x))
        (-(m62TangentRicci F c r x + m62CurvatureSquared F c r x)) r := by
    have hvne := (hpos r (Ioo_subset_Icc_self hr)).ne'
    convert! (c2ShrinkingCurve_speed_hasDerivAt_of_curvature_c1 F hc hH
      (hio hr) x).log hvne using 1
    field_simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hlog hderiv
    (ContinuousOn.intervalIntegrable_of_Icc hst hAcont).neg
  rw [intervalIntegral.integral_neg] at hFTC
  have hlogeq : Real.log (curveSpeed F c t x) = Real.log (curveSpeed F c s x) -
      ∫ r in s..t, m62TangentRicci F c r x + m62CurvatureSquared F c r x := by
    linarith
  calc
    _ = Real.exp (Real.log (curveSpeed F c t x)) :=
      (Real.exp_log (hpos t ⟨hst, le_rfl⟩)).symm
    _ = _ := by
      rw [hlogeq, sub_eq_add_neg, Real.exp_add, Real.exp_log (hpos s ⟨le_rfl, hst⟩)]

end PoincareConjecture.M63
