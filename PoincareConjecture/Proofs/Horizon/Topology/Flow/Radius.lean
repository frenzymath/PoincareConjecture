import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace Poincare.Topology



theorem exists_flow_time_of_positive_radius
    {M : Type*} [TopologicalSpace M] {p : M} {f : M → ℝ}
    (hf : Continuous f) (hzero : f p = 0) (hpos : ∀ y, y ≠ p → 0 < f y)
    (hcompact : ∀ R : ℝ, IsCompact {y | f y ≤ R})
    {Φ : ℝ → M → M} (hΦ : Continuous (Function.uncurry Φ))
    (hi : ∀ y, Φ 0 y = y) (hadd : ∀ s t y, Φ (s + t) y = Φ s (Φ t y))
    (hmono : ∀ y, y ≠ p → StrictMono (fun t => f (Φ t y)))
    {x : M} (hxp : x ≠ p) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, f (Φ t x) = r := by
  have hslice (t : ℝ) : Continuous (Φ t) := hΦ.comp (continuous_const.prodMk continuous_id)
  have hcurve : Continuous (fun t => f (Φ t x)) :=
    hf.comp (hΦ.comp (continuous_id.prodMk continuous_const))
  have hclosed (R : ℝ) : IsClosed {y | f y ≤ R} := isClosed_le hf continuous_const
  have hupper : ∃ t : ℝ, r ≤ f (Φ t x) := by
    by_contra! hfail
    let K : Set M := closure (range (fun t => Φ t x))
    have hK : IsCompact K := (hcompact r).of_isClosed_subset isClosed_closure
      (closure_minimal (by rintro y ⟨t, rfl⟩; exact (hfail t).le) (hclosed r))
    have hxK : x ∈ K := by
      apply subset_closure
      exact ⟨0, hi x⟩
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hf.continuousOn
    have hnext : Φ 1 y ∈ K := map_mem_closure (hslice 1) hy (by
      rintro z ⟨t, rfl⟩
      exact ⟨1 + t, hadd 1 t x⟩)
    have hyp : y ≠ p := by
      intro he
      have h := hmax hxK
      rw [he, hzero] at h
      exact (not_le_of_gt (hpos x hxp)) h
    have h := hmono y hyp (show (0 : ℝ) < 1 by norm_num)
    simp only [hi] at h
    exact (not_lt_of_ge (hmax hnext)) h
  have hlower : ∃ t : ℝ, f (Φ t x) ≤ r := by
    by_contra! hfail
    let K : Set M := closure ((fun t => Φ t x) '' Iic (0 : ℝ))
    have hK : IsCompact K := (hcompact (f x)).of_isClosed_subset isClosed_closure
      (closure_minimal (by
        rintro y ⟨t, ht, rfl⟩
        change f (Φ t x) ≤ f x
        simpa only [hi] using (hmono x hxp).monotone ht) (hclosed (f x)))
    have hxK : x ∈ K := subset_closure ⟨0, mem_Iic.mpr le_rfl, hi x⟩
    have hbound : K ⊆ {y | r ≤ f y} :=
      closure_minimal (by rintro y ⟨t, _, rfl⟩; exact (hfail t).le)
        (isClosed_le continuous_const hf)
    obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨x, hxK⟩ hf.continuousOn
    have hyp : y ≠ p := by
      intro he
      have h := hbound hy
      change r ≤ f y at h
      rw [he, hzero] at h
      exact (not_le_of_gt hr) h
    have hprev : Φ (-1) y ∈ K := map_mem_closure (hslice (-1)) hy (by
      rintro z ⟨t, ht, rfl⟩
      exact ⟨-1 + t, mem_Iic.mpr (by linarith [mem_Iic.mp ht]), hadd (-1) t x⟩)
    have h := hmono y hyp (show (-1 : ℝ) < 0 by norm_num)
    simp only [hi] at h
    exact (not_lt_of_ge (hmin hprev)) h
  obtain ⟨s, hs⟩ := hlower
  obtain ⟨t, ht⟩ := hupper
  exact intermediate_value_univ s t hcurve ⟨hs, ht⟩

end Poincare.Topology
