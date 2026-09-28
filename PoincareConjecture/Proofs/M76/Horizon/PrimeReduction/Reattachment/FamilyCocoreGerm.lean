import Mathlib.Topology.Separation.Basic

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem sphere_family_open_germ_after_exchange
    {X κ : Type*} [TopologicalSpace X] [DecidableEq κ]
    (S : κ → Set X) (i : κ)
    (hdis : Pairwise fun j k => Disjoint (S j) (S k))
    (N : Bool → Set X) (hNclosed : ∀ b, IsClosed (N b))
    (hNdis : Disjoint (N true) (N false))
    (C F : Set X) (hC : IsClosed C)
    (hCother : ∀ j, j ≠ i → Disjoint C (S j))
    (houtside : (N true ∪ N false) \ C = S i \ C)
    (hNsub : ∀ b, N b ⊆ S i ∪ C)
    (hNlevel : ∀ b, Disjoint (N b ∩ F) C) :
    ∀ b, ∃ G : Set X, IsOpen G ∧
      ((⋃ j, Function.update S i (N b) j) ∩ F) ⊆ G ∧
      ∀ x ∈ G, (x ∈ ⋃ j, Function.update S i (N b) j) ↔ x ∈ ⋃ j, S j := by
  intro b
  have hpair : Disjoint (N b) (N (!b)) := by
    cases b
    · exact hNdis.symm
    · exact hNdis
  have hother (j : κ) (hji : j ≠ i) : Disjoint (S j) (N (!b)) := by
    apply disjoint_left.mpr
    intro x hx hn
    rcases hNsub (!b) hn with hs | hc
    · exact disjoint_left.mp (hdis hji) hx hs
    · exact disjoint_left.mp (hCother j hji) hc hx
  refine ⟨(C ∪ N (!b))ᶜ,(hC.union (hNclosed (!b))).isOpen_compl,?_,?_⟩
  · rintro x ⟨hx,hxF⟩ (hc | hn)
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self] at hj
        exact disjoint_left.mp (hNlevel b) ⟨hj,hxF⟩ hc
      · simp only [Function.update_of_ne hji] at hj
        exact disjoint_left.mp (hCother j hji) hc hj
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self] at hj
        exact disjoint_left.mp hpair hj hn
      · simp only [Function.update_of_ne hji] at hj
        exact disjoint_left.mp (hother j hji) hj hn
  · intro x hx
    have hxC : x ∉ C := fun hc => hx (Or.inl hc)
    have hxN : x ∉ N (!b) := fun hn => hx (Or.inr hn)
    constructor
    · intro hnew
      obtain ⟨j,hj⟩ := mem_iUnion.mp hnew
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self] at hj
        apply mem_iUnion_of_mem i
        apply (houtside.subset ⟨?_,hxC⟩).1
        cases b
        · exact Or.inr hj
        · exact Or.inl hj
      · exact mem_iUnion_of_mem j (by simpa only [Function.update_of_ne hji] using hj)
    · intro hold
      obtain ⟨j,hj⟩ := mem_iUnion.mp hold
      by_cases hji : j = i
      · subst j
        have hn := (houtside.superset ⟨hj,hxC⟩).1
        apply mem_iUnion_of_mem i
        simp only [Function.update_self]
        cases b <;> simp only [Bool.not_false,Bool.not_true] at hxN
        · exact hn.resolve_left hxN
        · exact hn.resolve_right hxN
      · exact mem_iUnion_of_mem j (by simpa only [Function.update_of_ne hji] using hj)

end PoincareConjecture.M76
