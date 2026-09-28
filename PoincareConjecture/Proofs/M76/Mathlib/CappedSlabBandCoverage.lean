import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabLevelCoverage

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*}

theorem cut_slab_band_eq {S s T R : Set E} {A : E → ℝ} {β a b : ℝ}
    (hs : s ⊆ S) (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β})
    (ha : 0 ≤ a) (hb : b ≤ β) :
    ((T ∩ s) ∪ (R ∩ s)) ∩ {x | A x ∈ Icc a b} =
      s ∩ {x | A x ∈ Icc a b} := by
  ext x
  constructor
  · rintro ⟨hx | hx, hxA⟩ <;> exact ⟨hx.2, hxA⟩
  · intro hx
    have h := (cut_slab_level_eq hs hslab
      ⟨ha.trans hx.2.1, hx.2.2.trans hb⟩).symm.subset ⟨hx.1, rfl⟩
    exact ⟨h.1, hx.2⟩

theorem image_capped_slab_band_eq_of_cap_below
    {S s d T R : Set E} {A : E → ℝ} {β a b : ℝ}
    (hs : s ⊆ S) (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β})
    (f : E → E) (hraise : ∀ x ∈ s, A x ≤ A (f x))
    (hneg : ∀ x ∈ s, A x < 0 → f x = x) (hR : ∀ x ∈ R, f x = x)
    (ha : 0 < a) (hb : b ≤ β) (hcap : ∀ x ∈ d, A (f x) < a) :
    (f '' (s ∪ d)) ∩ {x | A x ∈ Icc a b} =
      ((f '' (T ∩ s)) ∪ (R ∩ s)) ∩ {x | A x ∈ Icc a b} := by
  ext x
  constructor
  · intro hx
    have h := (image_capped_slab_level_eq hs hslab f hraise hneg hR
      ⟨ha.trans_le hx.2.1, hx.2.2.trans hb⟩).subset ⟨hx.1, rfl⟩
    refine ⟨?_, hx.2⟩
    rcases h.1 with h | h
    · obtain ⟨y, hyd | hyT, hyx⟩ := h
      · exact ((hyx ▸ hcap y hyd).not_ge hx.2.1).elim
      · exact Or.inl ⟨y, hyT, hyx⟩
    · exact Or.inr h
  · rintro ⟨hxT | hxR, hxA⟩
    · exact ⟨image_mono (inter_subset_right.trans subset_union_left) hxT, hxA⟩
    · exact ⟨⟨x, Or.inl hxR.2, hR x hxR.1⟩, hxA⟩

end Set
