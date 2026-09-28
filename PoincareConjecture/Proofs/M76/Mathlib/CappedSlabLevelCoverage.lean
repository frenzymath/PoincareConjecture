import Mathlib.Topology.Instances.Real.Lemmas










set_option autoImplicit false

namespace Set

variable {E : Type*}




theorem cut_slab_level_eq {S s T R : Set E} {A : E → ℝ} {β c : ℝ}
    (hs : s ⊆ S) (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β})
    (hc : c ∈ Icc 0 β) :
    ((T ∩ s) ∪ (R ∩ s)) ∩ {x | A x = c} = s ∩ {x | A x = c} := by
  ext x
  constructor
  · rintro ⟨hx | hx, hxA⟩ <;> exact ⟨hx.2, hxA⟩
  · intro hx
    have hxTR : x ∈ T ∪ R := hslab.symm.subset
      ⟨hs hx.1, by change A x ∈ Icc 0 β; rwa [hx.2]⟩
    exact ⟨hxTR.imp (fun h => ⟨h, hx.1⟩) (fun h => ⟨h, hx.1⟩), hx.2⟩






theorem image_capped_slab_level_eq {S s d T R : Set E} {A : E → ℝ} {β c : ℝ}
    (hs : s ⊆ S) (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β})
    (f : E → E) (hraise : ∀ x ∈ s, A x ≤ A (f x))
    (hneg : ∀ x ∈ s, A x < 0 → f x = x) (hR : ∀ x ∈ R, f x = x)
    (hc : c ∈ Ioc 0 β) :
    (f '' (s ∪ d)) ∩ {x | A x = c} =
      ((f '' (d ∪ (T ∩ s))) ∪ (R ∩ s)) ∩ {x | A x = c} := by
  ext y
  constructor
  · rintro ⟨⟨x, hxs | hxd, rfl⟩, hxA⟩
    · have hxnonneg : 0 ≤ A x := by
        by_contra hn
        have hfix := hneg x hxs (lt_of_not_ge hn)
        rw [hfix] at hxA
        exact (not_le_of_gt hc.1) (hxA ▸ le_of_lt (lt_of_not_ge hn))
      have hxupper : A x ≤ β := (hraise x hxs).trans (hxA ▸ hc.2)
      have hxTR : x ∈ T ∪ R := hslab.symm.subset ⟨hs hxs, hxnonneg, hxupper⟩
      rcases hxTR with hxT | hxR
      · exact ⟨Or.inl ⟨x, Or.inr ⟨hxT, hxs⟩, rfl⟩, hxA⟩
      · exact ⟨Or.inr ((hR x hxR).symm ▸ And.intro hxR hxs), hxA⟩
    · exact ⟨Or.inl ⟨x, Or.inl hxd, rfl⟩, hxA⟩
  · rintro ⟨hy | hy, hyA⟩
    · obtain ⟨x, hxd | hxT, rfl⟩ := hy
      · exact ⟨⟨x, Or.inr hxd, rfl⟩, hyA⟩
      · exact ⟨⟨x, Or.inl hxT.2, rfl⟩, hyA⟩
    · exact ⟨⟨y, Or.inl hy.2, hR y hy.1⟩, hyA⟩

end Set
