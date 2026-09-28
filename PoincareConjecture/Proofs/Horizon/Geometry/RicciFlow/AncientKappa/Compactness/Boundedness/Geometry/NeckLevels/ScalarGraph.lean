import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace Poincare.Analysis

private theorem existsUnique_level_of_deriv_ge
    {F : ℝ → ℝ} {W m c : ℝ} (hW : 0 < W) (hm : 0 < m)
    (hF : ∀ t ∈ Icc (-W) W, ContDiffAt ℝ ∞ F t)
    (hderiv : ∀ t ∈ Icc (-W) W, m ≤ deriv F t)
    (hcenter : |F 0 - c| < m * W) :
    ∃! t : ℝ, t ∈ Ioo (-W) W ∧ F t = c := by
  have hcont : ContinuousOn F (Icc (-W) W) :=
    fun t ht => (hF t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Icc (-W) W)) :=
    fun t ht => ((hF t (interior_subset ht)).differentiableAt (by simp)).differentiableWithinAt
  have hzero : (0 : ℝ) ∈ Icc (-W) W := ⟨by linarith, hW.le⟩
  have hleft : -W ∈ Icc (-W) W := ⟨le_rfl, by linarith⟩
  have hright : W ∈ Icc (-W) W := ⟨by linarith, le_rfl⟩
  have hl := (convex_Icc (-W) W).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun t ht => hderiv t (interior_subset ht)) (-W) hleft 0 hzero (by linarith)
  have hr := (convex_Icc (-W) W).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun t ht => hderiv t (interior_subset ht)) 0 hzero W hright hW.le
  have hvalues : F (-W) < c ∧ c < F W := by
    have hc := abs_lt.mp hcenter
    constructor <;> nlinarith [hc.1, hc.2]
  obtain ⟨t, ht, htc⟩ := intermediate_value_Ioo (show -W ≤ W by linarith) hcont hvalues
  have hmono : StrictMonoOn F (Icc (-W) W) :=
    strictMonoOn_of_deriv_pos (convex_Icc (-W) W) hcont
      (fun t ht => hm.trans_le (hderiv t (interior_subset ht)))
  refine ⟨t, ⟨ht, htc⟩, ?_⟩
  intro s hs
  exact hmono.injOn ⟨hs.1.1.le, hs.1.2.le⟩ ⟨ht.1.le, ht.2.le⟩ (hs.2.trans htc.symm)

theorem existsUnique_level_of_abs_deriv_ge
    {F : ℝ → ℝ} {W m c : ℝ} (hW : 0 < W) (hm : 0 < m)
    (hF : ∀ t ∈ Icc (-W) W, ContDiffAt ℝ ∞ F t)
    (hderiv : ∀ t ∈ Icc (-W) W, m ≤ |deriv F t|)
    (hcenter : |F 0 - c| < m * W) :
    ∃! t : ℝ, t ∈ Ioo (-W) W ∧ F t = c := by
  have hcont : ContinuousOn (deriv F) (Icc (-W) W) := by
    intro t ht
    exact ((hF t ht).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hne (t : ℝ) (ht : t ∈ Icc (-W) W) : deriv F t ≠ 0 := by
    intro heq
    have hb := hderiv t ht
    rw [heq, abs_zero] at hb
    linarith
  rcases isPreconnected_Icc.mapsTo_Ioi_or_Iio hcont hne with hpos | hneg
  · exact existsUnique_level_of_deriv_ge hW hm hF
      (fun t ht => by
        have hp : 0 < deriv F t := hpos ht
        simpa only [abs_of_pos hp] using hderiv t ht) hcenter
  · have hFneg : ∀ t ∈ Icc (-W) W, ContDiffAt ℝ ∞ (fun s => -F s) t :=
      fun t ht => (hF t ht).neg
    have hnegderiv (t : ℝ) (ht : t ∈ Icc (-W) W) :
        m ≤ deriv (fun s => -F s) t := by
      rw [deriv.fun_neg]
      have hn : deriv F t < 0 := hneg ht
      simpa only [abs_of_neg hn] using hderiv t ht
    have hc : |(-F 0) - (-c)| < m * W := by
      simpa only [neg_sub_neg, abs_sub_comm] using hcenter
    obtain ⟨t, ht, huniq⟩ := existsUnique_level_of_deriv_ge hW hm hFneg hnegderiv hc
    refine ⟨t, ⟨ht.1, neg_injective ht.2⟩, ?_⟩
    intro s hs
    exact huniq s ⟨hs.1, congrArg Neg.neg hs.2⟩

end Poincare.Analysis
