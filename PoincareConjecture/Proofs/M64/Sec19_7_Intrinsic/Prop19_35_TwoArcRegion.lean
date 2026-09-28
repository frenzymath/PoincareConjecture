import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanRegion
import Mathlib.Topology.Piecewise













noncomputable section
set_option autoImplicit false

open Set Function Metric
open scoped Topology

namespace PoincareConjecture





theorem m64Intrinsic_exists_region_between_arcs
    {α β : ℝ → AnnulusCoordinates}
    (hαc : ContinuousOn α (Icc 0 1)) (hβc : ContinuousOn β (Icc 0 1))
    (hαinj : InjOn α (Icc 0 1)) (hβinj : InjOn β (Icc 0 1))
    (h0 : α 0 = β 0) (h1 : α 1 = β 1)
    (hmeet : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      α s = β t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (α '' Icc 0 1 ∪ β '' Icc 0 1)ᶜ ∧
      frontier U = α '' Icc 0 1 ∪ β '' Icc 0 1 ∧
      frontier V = α '' Icc 0 1 ∪ β '' Icc 0 1 ∧ IsCompact (closure U) := by
  classical
  let γ : ℝ → AnnulusCoordinates := fun t => if t ≤ 1 then α t else β (2 - t)
  have hγc : ContinuousOn γ (Icc 0 2) := by
    apply ContinuousOn.if
    · intro t ht
      have ht' : t = 1 := by
        have h := ht.2
        change t ∈ frontier (Iic (1 : ℝ)) at h
        simpa only [frontier_Iic, mem_singleton_iff] using h
      subst t
      convert h1 using 1
      norm_num
    · apply hαc.mono
      intro t ht
      exact ⟨ht.1.1, by simpa only [show {a : ℝ | a ≤ 1} = Iic 1 from rfl,
        isClosed_Iic.closure_eq, mem_Iic] using ht.2⟩
    · apply hβc.comp (continuous_const.sub continuous_id).continuousOn
      intro t ht
      have ht1 : 1 ≤ t := by
        have h := ht.2
        simp only [not_le] at h
        change t ∈ closure (Ioi (1 : ℝ)) at h
        simpa only [closure_Ioi, mem_Ici] using h
      change 2 - t ∈ Icc 0 1
      exact ⟨by linarith [ht.1.2], by linarith⟩
  have hγ0 : γ 0 = α 0 := by norm_num [γ]
  have hγ2 : γ 2 = β 0 := by norm_num [γ]
  have hγend : γ 0 = γ 2 := hγ0.trans (h0.trans hγ2.symm)
  have hγinj : InjOn γ (Ico 0 2) := by
    intro s hs t ht heq
    wlog hst : s ≤ t generalizing s t
    · exact (this ht hs heq.symm (le_of_not_ge hst)).symm
    by_cases ht1 : t ≤ 1
    · have hs1 : s ≤ 1 := hst.trans ht1
      apply hαinj ⟨hs.1, hs1⟩ ⟨ht.1, ht1⟩
      simpa only [γ, if_pos hs1, if_pos ht1] using heq
    · by_cases hs1 : s ≤ 1
      · have h := hmeet s ⟨hs.1, hs1⟩ (2 - t)
          ⟨by linarith [ht.2], by linarith⟩
          (by simpa only [γ, if_pos hs1, if_neg ht1] using heq)
        rcases h with ⟨_, ht0⟩ | ⟨_, ht'⟩
        · linarith [ht.2]
        · linarith
      · have h := hβinj (x₁ := 2 - s) (x₂ := 2 - t)
          ⟨by linarith [hs.2], by linarith⟩
          ⟨by linarith [ht.2], by linarith⟩
          (by simpa only [γ, if_neg hs1, if_neg ht1] using heq)
        linarith
  have hγimage : γ '' Icc 0 2 = α '' Icc 0 1 ∪ β '' Icc 0 1 := by
    apply Subset.antisymm
    · rintro p ⟨t, ht, rfl⟩
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨t, ⟨ht.1, ht1⟩, (if_pos ht1).symm⟩
      · exact Or.inr ⟨2 - t, ⟨by linarith [ht.2], by linarith⟩, (if_neg ht1).symm⟩
    · rintro p (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, if_pos ht.2⟩
      · refine ⟨2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
        by_cases ht1 : t = 1
        · subst t
          norm_num [γ]
          exact h1
        · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
          rw [show γ (2 - t) = β (2 - (2 - t)) from if_neg (by linarith)]
          congr 1
          ring
  obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj, hunion, hfU, hfV, hcompact⟩ :=
    m64Intrinsic_exists_jordan_region (by norm_num : (0 : ℝ) < 2) hγc hγend hγinj
  rw [hγimage] at hunion hfU hfV
  exact ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj, hunion, hfU, hfV, hcompact⟩

end PoincareConjecture
