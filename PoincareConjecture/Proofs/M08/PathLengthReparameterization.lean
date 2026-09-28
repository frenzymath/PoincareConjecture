import PoincareConjecture.Proofs.M08.PathTightness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.M08

theorem exists_lipschitz_length_reparameterization {X : Type*} [MetricSpace X]
    (α : ℝ → X) (v : ℝ → ℝ) (hv : ContinuousOn v (Icc 0 1))
    (hnonneg : ∀ t ∈ Icc 0 1, 0 ≤ v t)
    (hinc : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1, s ≤ t →
      dist (α s) (α t) ≤ ∫ r in s..t, v r) :
    ∃ β : Icc (0 : ℝ) 1 → X,
      β ⟨0, le_rfl, zero_le_one⟩ = α 0 ∧
      β ⟨1, zero_le_one, le_rfl⟩ = α 1 ∧
      ∀ s t, dist (β s) (β t) ≤ (1 + ∫ r in (0 : ℝ)..1, v r) * dist s t := by
  classical
  let L := ∫ r in (0 : ℝ)..1, v r
  let H := fun t : ℝ ↦ t + ∫ r in (0 : ℝ)..t, v r
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg zero_le_one hnonneg
  have hint (s t : ℝ) (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
      IntervalIntegrable v volume s t := by
    apply ContinuousOn.intervalIntegrable
    exact hv.mono (uIcc_subset_Icc hs ht)
  have hHcont : ContinuousOn H (Icc 0 1) := by
    apply continuousOn_id.add
    simpa only [uIcc_of_le zero_le_one] using
      intervalIntegral.continuousOn_primitive_interval' (hint 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩)
        (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 1)
  have hHdiff (s t : ℝ) (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
      H t - H s = t - s + ∫ r in s..t, v r := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hint 0 s ⟨le_rfl, zero_le_one⟩ hs) (hint s t hs ht)
    dsimp only [H]
    linarith
  have hHmono : StrictMonoOn H (Icc 0 1) := by
    intro s hs t ht hst
    have hnon := intervalIntegral.integral_nonneg (μ := volume) hst.le
      (fun r hr ↦ hnonneg r ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩)
    have h := hHdiff s t hs ht
    linarith
  have hH0 : H 0 = 0 := by simp [H]
  have hH1 : H 1 = 1 + L := rfl
  have hsurj (t : Icc (0 : ℝ) 1) : ∃ r ∈ Icc 0 1, H r = (1 + L) * t := by
    have hmem : (1 + L) * t ∈ Icc (H 0) (H 1) := by
      rw [hH0, hH1]
      exact ⟨mul_nonneg (by linarith) t.2.1,
        (mul_le_mul_of_nonneg_left t.2.2 (by linarith)).trans_eq (mul_one _)⟩
    rw [← hHcont.image_Icc_of_monotoneOn zero_le_one hHmono.monotoneOn] at hmem
    exact hmem
  choose r hr hreq using hsurj
  have hr0 : r ⟨0, le_rfl, zero_le_one⟩ = 0 := by
    apply hHmono.injOn (hr _) ⟨le_rfl, zero_le_one⟩
    rw [hreq, hH0, mul_zero]
  have hr1 : r ⟨1, zero_le_one, le_rfl⟩ = 1 := by
    apply hHmono.injOn (hr _) ⟨zero_le_one, le_rfl⟩
    rw [hreq, hH1, mul_one]
  have hrmono {s t : Icc (0 : ℝ) 1} (hst : s ≤ t) : r s ≤ r t := by
    by_contra h
    have hlt := hHmono (hr t) (hr s) (lt_of_not_ge h)
    rw [hreq, hreq] at hlt
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (show (s : ℝ) ≤ t from hst)
      (show (0 : ℝ) ≤ 1 + L by linarith))) hlt
  have hbound (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
      dist (α (r s)) (α (r t)) ≤ (1 + L) * ((t : ℝ) - s) := by
    have hrs := hrmono hst
    have hd := hHdiff (r s) (r t) (hr s) (hr t)
    rw [hreq, hreq] at hd
    have h := hinc (r s) (hr s) (r t) (hr t) hrs
    nlinarith
  refine ⟨fun t ↦ α (r t), congrArg α hr0, congrArg α hr1, ?_⟩
  intro s t
  rcases le_total s t with hst | hts
  · simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm (s : ℝ),
      abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))] using hbound s t hst
  · simpa only [dist_comm (α (r t)), Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ s from hts))] using hbound t s hts

end PoincareConjecture.M08
