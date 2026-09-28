import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.RetainedComponentContainment









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn



theorem whole_components_of_selected_strip_pair
    {E I : Type*} [TopologicalSpace E] {S G A M C B0 B1 : Set E}
    (U : I → Set E) (a b : I)
    (hA : IsClosed A) (hM : IsClosed M) (hC : IsClosed C)
    (hAM : Disjoint A M) (hMC : Disjoint M C) (hAC : Disjoint A C)
    (hcover : ((A ∪ M) ∪ C) ∪ (B0 ∪ B1) = S)
    (hG : ⋃ i, U i = G) (hGS : G ⊆ S)
    (hconn : ∀ i, IsConnected (U i))
    (hdisj : Pairwise (fun i l ↦ Disjoint (U i) (U l)))
    (hstrip : G ∩ (B0 ∪ B1) ⊆ U a ∪ U b)
    (ha : Disjoint (U a) ((A ∪ M) ∪ C))
    (hb : Disjoint (U b) ((A ∪ M) ∪ C)) :
    (∀ i, U i ⊆ A ∪ C ∨ Disjoint (U i) (A ∪ C)) ∧
      (∀ i, U i ⊆ (A ∪ M) ∪ C ∨ Disjoint (U i) ((A ∪ M) ∪ C)) := by
  have hsub (i : I) : U i ⊆ G := by
    rw [← hG]
    exact subset_iUnion U i
  have hsmall : A ∪ C ⊆ (A ∪ M) ∪ C := by
    rintro x (hx | hx)
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
  have hcases (i : I) :
      (Disjoint (U i) ((A ∪ M) ∪ C)) ∨
      ((U i ⊆ A ∧ Disjoint (U i) M ∧ Disjoint (U i) C) ∨
        (U i ⊆ M ∧ Disjoint (U i) A ∧ Disjoint (U i) C) ∨
        (U i ⊆ C ∧ Disjoint (U i) A ∧ Disjoint (U i) M)) := by
    by_cases hia : i = a
    · subst i
      exact Or.inl ha
    by_cases hib : i = b
    · subst i
      exact Or.inl hb
    have hoff : Disjoint (U i) (B0 ∪ B1) := by
      apply disjoint_left.mpr
      intro x hx hxB
      rcases hstrip ⟨hsub i hx, hxB⟩ with hxa | hxb
      · exact disjoint_left.mp (hdisj hia) hx hxa
      · exact disjoint_left.mp (hdisj hib) hx hxb
    exact Or.inr (connected_component_in_one_exterior hA hM hC hAM hMC hAC
      hcover (hconn i) ((hsub i).trans hGS) hoff)
  constructor
  · intro i
    rcases hcases i with h | ⟨h, _, _⟩ | ⟨_, hA', hC'⟩ | ⟨h, _, _⟩
    · exact Or.inr (h.mono_right hsmall)
    · exact Or.inl (h.trans subset_union_left)
    · exact Or.inr (disjoint_union_right.mpr ⟨hA', hC'⟩)
    · exact Or.inl (h.trans subset_union_right)
  · intro i
    rcases hcases i with h | ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨h, _, _⟩
    · exact Or.inr h
    · exact Or.inl (h.trans (subset_union_left.trans subset_union_left))
    · exact Or.inl (h.trans (subset_union_right.trans subset_union_left))
    · exact Or.inl (h.trans subset_union_right)

end PoincareConjecture.M76.Dehn
