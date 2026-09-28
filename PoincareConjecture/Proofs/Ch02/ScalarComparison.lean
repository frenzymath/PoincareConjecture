import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture

theorem compact_min_velocity_lower_bound
    {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {a b r0 : ℝ} {n : ℕ}
    (_hab : a < b) (hn : 0 < n) (hr0 : r0 < 0)
    (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Ico a b ×ˢ (univ : Set M)))
    (hderiv : ∀ t ∈ Ico a b, ∀ x : M,
      HasDerivWithinAt (fun s : ℝ ↦ f s x) (v t x) (Ico a b) t)
    (hmin : ∀ t ∈ Ico a b, ∀ x : M,
      (∀ y : M, f t x ≤ f t y) → (2 / (n : ℝ)) * (f t x) ^ 2 ≤ v t x)
    (hinit : ∀ x : M, r0 ≤ f a x) :
    ∀ t ∈ Ico a b, ∀ x : M,
      r0 / (1 - 2 * r0 * (t - a) / (n : ℝ)) ≤ f t x := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let r : ℝ → ℝ := fun s ↦ r0 / (1 - 2 * r0 * (s - a) / (n : ℝ))
  have hden (s : ℝ) (hs : a ≤ s) : 0 < 1 - 2 * r0 * (s - a) / (n : ℝ) := by
    have hprod : 2 * r0 * (s - a) / (n : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hs)) hnR.le
    linarith
  have hr (s : ℝ) (hs : a ≤ s) : r s < 0 := div_neg_of_neg_of_pos hr0 (hden s hs)
  have hra : r a = r0 := by simp [r]
  have hrderiv (s : ℝ) (hs : a ≤ s) :
      HasDerivAt r ((2 / (n : ℝ)) * (r s) ^ 2) s := by
    have hd := (hasDerivAt_const s (1 : ℝ)).sub
      ((((hasDerivAt_id s).sub_const a).const_mul (2 * r0)).div_const (n : ℝ))
    convert! (hasDerivAt_const s r0).div hd (ne_of_gt (hden s hs)) using 1
    dsimp [r]
    field_simp
    ring
  intro t ht x
  by_contra hbad
  have hbad' : f t x < r t := lt_of_not_ge hbad
  let K : Set (ℝ × M) := Icc a t ×ˢ univ
  have hsub : K ⊆ Ico a b ×ˢ (univ : Set M) :=
    fun p hp ↦ ⟨⟨hp.1.1, hp.1.2.trans_lt ht.2⟩, hp.2⟩
  have hrc : ContinuousOn (fun p : ℝ × M ↦ r p.1) K :=
    (show ContinuousOn r (Icc a t) from
      fun s hs ↦ (hrderiv s hs.1).continuousAt.continuousWithinAt).comp
        continuous_fst.continuousOn (fun _ hp ↦ hp.1)
  have hwc : ContinuousOn (fun p : ℝ × M ↦ f p.1 p.2 - r p.1) K :=
    (hf.mono hsub).sub hrc
  obtain ⟨⟨s, y⟩, hsy, hminw⟩ := (isCompact_Icc.prod isCompact_univ).exists_isMinOn
    (show K.Nonempty from ⟨(a, x), ⟨⟨le_rfl, ht.1⟩, mem_univ x⟩⟩) hwc
  change (s ∈ Icc a t) ∧ y ∈ (univ : Set M) at hsy
  have hwy : f s y - r s < 0 :=
    (hminw (show (t, x) ∈ K from ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩)).trans_lt
      (sub_neg.mpr hbad')
  have hsa : a < s := by
    rcases lt_or_eq_of_le hsy.1.1 with hsa | hsa
    · exact hsa
    · rw [← hsa, hra] at hwy
      exact False.elim ((not_lt_of_ge (sub_nonneg.mpr (hinit y))) hwy)
  have hsJ : s ∈ Ico a b := ⟨hsa.le, hsy.1.2.trans_lt ht.2⟩
  have hspace : ∀ z : M, f s y ≤ f s z := by
    intro z
    have h := hminw (show (s, z) ∈ K from ⟨hsy.1, mem_univ z⟩)
    change f s y - r s ≤ f s z - r s at h
    linarith
  have hpos : 0 < v s y - (2 / (n : ℝ)) * (r s) ^ 2 := by
    have hsq : (r s) ^ 2 < (f s y) ^ 2 := by
      have := hr s hsa.le
      nlinarith
    have hmul := mul_lt_mul_of_pos_left hsq (div_pos (by norm_num : (0 : ℝ) < 2) hnR)
    have := hmin s hsJ y hspace
    linarith
  have htime : IsMinOn (fun q : ℝ ↦ f q y - r q) (Icc a s) s := by
    intro q hq
    exact hminw (show (q, y) ∈ K from ⟨⟨hq.1, hq.2.trans hsy.1.2⟩, mem_univ y⟩)
  have hdw : HasDerivWithinAt (fun q : ℝ ↦ f q y - r q)
      (v s y - (2 / (n : ℝ)) * (r s) ^ 2) (Icc a s) s :=
    ((hderiv s hsJ y).mono fun q hq ↦ ⟨hq.1, hq.2.trans_lt hsJ.2⟩).sub
      (hrderiv s hsa.le).hasDerivWithinAt
  have hcone : a - s ∈ posTangentConeAt (Icc a s) s :=
    sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hsa.le])
  have hsign : 0 ≤ (a - s) * (v s y - (2 / (n : ℝ)) * (r s) ^ 2) := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      using htime.localize.hasFDerivWithinAt_nonneg hdw hcone
  exact (not_le_of_gt (mul_neg_of_neg_of_pos (sub_neg.mpr hsa) hpos)) hsign

end PoincareConjecture
