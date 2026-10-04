import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.IntegratedEnergy
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# The actual coordinate primitive at one corner

Morgan--Tian Claim 16.27, pp. 391-394. The minimizing prefix and
the short seed segment meet continuously at one positive square time.
Their coordinate derivative belongs to L2, and interval additivity
gives its primitive without assuming differentiability at the corner.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal intervalIntegral

namespace PoincareMT.M08
export PoincareMT.LGeometry (continuousOn_memLp_top_Icc)
end PoincareMT.M08
namespace PoincareMT.M08
export PoincareMT.LGeometry (ChartL2)
end PoincareMT.M08

namespace PoincareMT.Proofs.M46

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A C1 coordinate curve has an actual L2 derivative on its closed
parameter interval. The endpoint values of the derivative are immaterial. -/
theorem contDiffOn_deriv_memLp_Icc {a b : ℝ} {f : ℝ → E}
    (hab : a ≤ b) (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    MemLp (deriv f) 2 (volume.restrict (Icc a b)) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hcont := (hf.derivWithin (m := 0) (uniqueDiffOn_Icc hab) (by simp)).continuousOn
  have hLp : MemLp (derivWithin f (Icc a b)) 2 (volume.restrict (Icc a b)) :=
    (M08.continuousOn_memLp_top_Icc hcont).mono_exponent le_top
  apply (memLp_congr_ae ?_).mp hLp
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)

/-- A single continuous corner preserves the actual L2 coordinate
primitive. Its L2 representative agrees with the ordinary derivative
almost everywhere, including on intervals that straddle the corner. -/
theorem oneCorner_chartL2_primitive {a c b : ℝ} {f : ℝ → E}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hleft : ContDiffOn ℝ 1 f (Icc a c))
    (hright : ContDiffOn ℝ 1 f (Icc c b)) :
    ∃ v : M08.ChartL2 E a b,
      (v : ℝ → E) =ᵐ[volume.restrict (Icc a b)] deriv f ∧
      ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, v s := by
  have hL := contDiffOn_deriv_memLp_Icc hac hleft
  have hR := contDiffOn_deriv_memLp_Icc hcb hright
  have hmeas : AEStronglyMeasurable (deriv f) (volume.restrict (Icc a b)) := by
    rw [← Icc_union_Icc_eq_Icc hac hcb, aestronglyMeasurable_union_iff]
    exact ⟨hL.aestronglyMeasurable, hR.aestronglyMeasurable⟩
  have hLp : MemLp (deriv f) 2 (volume.restrict (Icc a b)) := by
    apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
    rw [← Icc_union_Icc_eq_Icc hac hcb]
    exact IntegrableOn.union
      ((memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL)
      ((memLp_two_iff_integrable_sq_norm hR.aestronglyMeasurable).mp hR)
  refine ⟨hLp.toLp (deriv f), hLp.coeFn_toLp, ?_⟩
  intro t ht
  have hint : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hac.trans hcb)).mpr
      (hLp.integrable (by norm_num))
  have heq : (∫ s in a..t, hLp.toLp (deriv f) s) = ∫ s in a..t, deriv f s := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    exact ae_mono (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)) le_rfl) hLp.coeFn_toLp
  rw [heq]
  have hFTC : (∫ s in a..t, deriv f s) = f t - f a := by
    by_cases htc : t ≤ c
    · exact intervalIntegral.integral_deriv_of_contDiffOn_Icc
        (hleft.mono (Icc_subset_Icc_right htc)) ht.1
    · have hct : c ≤ t := (lt_of_not_ge htc).le
      have hIntL := hint.mono_set (by
        rw [uIcc_of_le hac, uIcc_of_le (hac.trans hcb)]
        exact Icc_subset_Icc_right hcb)
      have hIntR := hint.mono_set (by
        rw [uIcc_of_le hct, uIcc_of_le (hac.trans hcb)]
        exact Icc_subset_Icc hac ht.2)
      rw [← intervalIntegral.integral_add_adjacent_intervals hIntL hIntR,
        intervalIntegral.integral_deriv_of_contDiffOn_Icc hleft hac,
        intervalIntegral.integral_deriv_of_contDiffOn_Icc
          (hright.mono (Icc_subset_Icc_right ht.2)) hct]
      abel
  rw [hFTC]
  abel

/-- Restricting a one-corner curve to any closed subinterval retains
its primitive, whether or not that subinterval contains the corner. -/
theorem oneCorner_chartL2_primitive_on {a b c : ℝ} {f : ℝ → E}
    (hab : a ≤ b)
    (hleft : ContDiffOn ℝ 1 f (Icc a b ∩ Iic c))
    (hright : ContDiffOn ℝ 1 f (Icc a b ∩ Ici c)) :
    ∃ v : M08.ChartL2 E a b,
      (v : ℝ → E) =ᵐ[volume.restrict (Icc a b)] deriv f ∧
      ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, v s := by
  by_cases hca : c ≤ a
  · have hfull := hright.mono (fun _ hs => ⟨hs, hca.trans hs.1⟩)
    exact oneCorner_chartL2_primitive (le_refl a) hab
      (hfull.mono (Icc_subset_Icc_right hab)) hfull
  by_cases hbc : b ≤ c
  · have hfull := hleft.mono (fun _ hs => ⟨hs, hs.2.trans hbc⟩)
    exact oneCorner_chartL2_primitive hab (le_refl b) hfull
      (hfull.mono (Icc_subset_Icc_left hab))
  have hac := (lt_of_not_ge hca).le
  have hcb := (lt_of_not_ge hbc).le
  apply oneCorner_chartL2_primitive hac hcb
  · exact hleft.mono (fun _ hs => ⟨⟨hs.1, hs.2.trans hcb⟩, hs.2⟩)
  · exact hright.mono (fun _ hs => ⟨⟨hac.trans hs.1, hs.2⟩, hs.1⟩)

end PoincareMT.Proofs.M46
