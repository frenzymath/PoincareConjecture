import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff intervalIntegral

namespace PoincareConjecture.M08

def variationParameterDeriv (C P : Set ℝ) (L : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  fderivWithin ℝ L (C ×ˢ P) z (0, 1)

theorem variationParameterDeriv_contDiffOn {C P : Set ℝ}
    (hC : UniqueDiffOn ℝ C) (hP : IsOpen P) (L : ℝ × ℝ → ℝ)
    (hL : ContDiffOn ℝ ∞ L (C ×ˢ P)) :
    ContDiffOn ℝ ∞ (variationParameterDeriv C P L) (C ×ˢ P) :=
  (hL.fderivWithin (hC.prod hP.uniqueDiffOn) (by simp)).clm_apply contDiffOn_const

theorem hasDerivAt_variationParameter {C P : Set ℝ} (hP : IsOpen P)
    (L : ℝ × ℝ → ℝ) (hL : ContDiffOn ℝ ∞ L (C ×ˢ P))
    {s u : ℝ} (hs : s ∈ C) (hu : u ∈ P) :
    HasDerivAt (fun v ↦ L (s, v)) (variationParameterDeriv C P L (s, u)) u := by
  have hd := ((hL (s, u) ⟨hs, hu⟩).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hi : HasDerivWithinAt (fun v : ℝ ↦ (s, v)) (0, 1) P u :=
    (hasDerivWithinAt_const u P s).prodMk (hasDerivWithinAt_id u P)
  exact (hd.comp_hasDerivWithinAt u hi (fun v hv ↦ ⟨hs, hv⟩)).hasDerivAt
    (hP.mem_nhds hu)

theorem hasDerivAt_variationIntegral {a b : ℝ} (hab : a < b)
    {P : Set ℝ} (hP : IsOpen P) (L : ℝ × ℝ → ℝ)
    (hL : ContDiffOn ℝ ∞ L (Icc a b ×ˢ P)) {u : ℝ} (hu : u ∈ P) :
    HasDerivAt (fun v ↦ ∫ s in a..b, L (s, v))
      (∫ s in a..b, variationParameterDeriv (Icc a b) P L (s, u)) u := by
  let L' := variationParameterDeriv (Icc a b) P L
  have hL' : ContDiffOn ℝ ∞ L' (Icc a b ×ˢ P) :=
    variationParameterDeriv_contDiffOn (uniqueDiffOn_Icc hab) hP L hL
  have hslice (v : ℝ) (hv : v ∈ P) : ContinuousOn (fun s ↦ L (s, v)) (Icc a b) :=
    hL.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      (fun s hs ↦ ⟨hs, hv⟩)
  have hslice' (v : ℝ) (hv : v ∈ P) : ContinuousOn (fun s ↦ L' (s, v)) (Icc a b) :=
    hL'.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      (fun s hs ↦ ⟨hs, hv⟩)
  obtain ⟨l, r, hulr, hnear, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (hP.mem_nhds hu)
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod (isCompact_Icc : IsCompact (Icc l r))).exists_bound_of_continuousOn
    (hL'.continuousOn.mono (prod_mono Subset.rfl hsub))
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v s ↦ L (s, v)) (F' := fun v s ↦ L' (s, v))
    (bound := fun _ ↦ K) hnear ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [hP.mem_nhds hu] with v hv
    exact ((hslice v hv).intervalIntegrable_of_Icc hab.le).aestronglyMeasurable_restrict_uIoc
  · exact (hslice u hu).intervalIntegrable_of_Icc hab.le
  · exact ((hslice' u hu).intervalIntegrable_of_Icc hab.le).aestronglyMeasurable_restrict_uIoc
  · exact Eventually.of_forall (fun s hs v hv ↦ hK (s, v)
      ⟨Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab.le] using hs), hv⟩)
  · exact Eventually.of_forall (fun s hs v hv ↦ hasDerivAt_variationParameter hP L hL
      (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab.le] using hs)) (hsub hv))

theorem hasDerivAt_deriv_variationIntegral {a b : ℝ} (hab : a < b)
    {P : Set ℝ} (hP : IsOpen P) (L : ℝ × ℝ → ℝ)
    (hL : ContDiffOn ℝ ∞ L (Icc a b ×ˢ P)) {u : ℝ} (hu : u ∈ P) :
    HasDerivAt (fun v ↦ deriv (fun w ↦ ∫ s in a..b, L (s, w)) v)
      (∫ s in a..b, variationParameterDeriv (Icc a b) P
        (variationParameterDeriv (Icc a b) P L) (s, u)) u := by
  have hd := hasDerivAt_variationIntegral hab hP (variationParameterDeriv (Icc a b) P L)
    (variationParameterDeriv_contDiffOn (uniqueDiffOn_Icc hab) hP L hL) hu
  apply hd.congr_of_eventuallyEq
  filter_upwards [hP.mem_nhds hu] with v hv
  exact (hasDerivAt_variationIntegral hab hP L hL hv).deriv

end PoincareConjecture.M08
