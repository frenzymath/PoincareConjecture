import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]




theorem hasDerivAt_integral_of_continuousOn_parameter {a b : ℝ} (hab : a ≤ b)
    {P : Set ℝ} (hP : IsOpen P) (L L' : ℝ × ℝ → E)
    (hL : ContinuousOn L (Icc a b ×ˢ P)) (hL' : ContinuousOn L' (Icc a b ×ˢ P))
    (hd : ∀ s ∈ Icc a b, ∀ v ∈ P, HasDerivAt (fun w => L (s, w)) (L' (s, v)) v)
    {v : ℝ} (hv : v ∈ P) :
    IntervalIntegrable (fun s => L' (s, v)) μ a b ∧
      HasDerivAt (fun w => ∫ s in a..b, L (s, w) ∂μ)
        (∫ s in a..b, L' (s, v) ∂μ) v := by
  have hslice (w : ℝ) (hw : w ∈ P) : ContinuousOn (fun s => L (s, w)) (Icc a b) :=
    hL.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, hw⟩)
  have hslice' (w : ℝ) (hw : w ∈ P) : ContinuousOn (fun s => L' (s, w)) (Icc a b) :=
    hL'.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, hw⟩)
  obtain ⟨l, r, _, hnear, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hP.mem_nhds hv)
  have hcompact : IsCompact (Icc a b ×ˢ Icc l r) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨K, hK⟩ := hcompact.exists_bound_of_continuousOn
    (hL'.mono (prod_mono Subset.rfl hsub))
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w s => L (s, w)) (F' := fun w s => L' (s, w))
    (bound := fun _ => K) hnear ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hP.mem_nhds hv] with w hw
    exact ((hslice w hw).intervalIntegrable_of_Icc hab).aestronglyMeasurable_restrict_uIoc
  · exact (hslice v hv).intervalIntegrable_of_Icc hab
  · exact ((hslice' v hv).intervalIntegrable_of_Icc hab).aestronglyMeasurable_restrict_uIoc
  · exact Eventually.of_forall (fun s hs w hw => hK (s, w)
      ⟨Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hs), hw⟩)
  · exact Eventually.of_forall (fun s hs w hw => hd s
      (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hs)) w (hsub hw))

end intervalIntegral
