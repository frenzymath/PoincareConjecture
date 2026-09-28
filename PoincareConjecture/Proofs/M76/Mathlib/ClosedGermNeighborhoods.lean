import Mathlib.Topology.Separation.Regular










set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X] [NormalSpace X]




theorem IsClosed.exists_open_neighborhoods_inter_subset {A B U V W : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hU : IsOpen U) (hV : IsOpen V)
    (hW : IsOpen W) (hAU : A ⊆ U) (hBV : B ⊆ V) (hAB : A ∩ B ⊆ W) :
    ∃ U' V' : Set X, IsOpen U' ∧ IsOpen V' ∧ A ⊆ U' ∧ B ⊆ V' ∧
      U' ⊆ U ∧ V' ⊆ V ∧ U' ∩ V' ⊆ W := by
  have hd : Disjoint (A \ W) (B \ W) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hx.2 (hAB ⟨hx.1, hy.1⟩)
  obtain ⟨U0, V0, hU0, hV0, hAU0, hBV0, hdisj⟩ :=
    normal_separation (hA.inter hW.isClosed_compl) (hB.inter hW.isClosed_compl) hd
  refine ⟨U ∩ (W ∪ U0), V ∩ (W ∪ V0), hU.inter (hW.union hU0),
    hV.inter (hW.union hV0), ?_, ?_, inter_subset_left, inter_subset_left, ?_⟩
  · intro x hx
    refine ⟨hAU hx, ?_⟩
    by_cases hxw : x ∈ W
    · exact Or.inl hxw
    · exact Or.inr (hAU0 ⟨hx, hxw⟩)
  · intro x hx
    refine ⟨hBV hx, ?_⟩
    by_cases hxw : x ∈ W
    · exact Or.inl hxw
    · exact Or.inr (hBV0 ⟨hx, hxw⟩)
  · rintro x ⟨⟨_, hx | hx⟩, ⟨_, hy | hy⟩⟩
    · exact hx
    · exact hx
    · exact hy
    · exact (disjoint_left.mp hdisj hx hy).elim
