import Mathlib.Order.Preorder.Finite
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence








set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem subset_interior_of_subset_of_disjoint_frontiers
    {X : Type*} [TopologicalSpace X] {Q P : Set X}
    (hQP : Q ⊆ P) (hdis : Disjoint (frontier Q) (frontier P)) : Q ⊆ interior P := by
  intro x hx
  apply (mem_interior_iff_notMem_frontier (hQP hx)).mpr
  intro hxP
  by_cases hxQ : x ∈ frontier Q
  · exact disjoint_left.mp hdis hxQ hxP
  · exact hxP.2 (interior_mono hQP ((mem_interior_iff_notMem_frontier hx).mpr hxQ))

theorem exists_outermost_sphere_ball_subfamily
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    (Q : κ → Set X) (hne : ∀ i, (frontier (Q i)).Nonempty)
    (hfront : Pairwise fun i j => Disjoint (frontier (Q i)) (frontier (Q j)))
    (hnested : ∀ i j, Disjoint (Q i) (Q j) ∨ Q i ⊆ Q j ∨ Q j ⊆ Q i) :
    ∃ t : Finset κ,
      Pairwise (fun i j : t => Disjoint (Q i) (Q j)) ∧
      (∀ i, ∃ j : t, Q i ⊆ Q j) ∧
      (⋃ j : t, Q j) = ⋃ i, Q i ∧
      (⋃ j : t, interior (Q j)) = ⋃ i, interior (Q i) ∧
      ∀ i, i ∉ t → ∃ j : t, Q i ⊆ interior (Q j) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hinj : Function.Injective Q := by
    intro i j heq
    by_contra hn
    obtain ⟨x,hx⟩ := hne i
    exact disjoint_left.mp (hfront hn) hx (heq ▸ hx)
  let t : Finset κ := Finset.univ.filter fun i => ∀ j, Q i ⊆ Q j → Q j ⊆ Q i
  have ht (i : κ) : i ∈ t ↔ ∀ j, Q i ⊆ Q j → Q j ⊆ Q i := by simp [t]
  have hcover (i : κ) : ∃ j : t, Q i ⊆ Q j := by
    obtain ⟨P,hiP,hmax⟩ := (finite_range Q).exists_le_maximal (mem_range_self i)
    obtain ⟨j,rfl⟩ := hmax.1
    have hj : j ∈ t := (ht j).mpr fun k hk => hmax.2 (mem_range_self k) hk
    exact ⟨⟨j,hj⟩,hiP⟩
  have hdis : Pairwise fun i j : t => Disjoint (Q i) (Q j) := by
    intro i j hij
    rcases hnested i j with hd | hsub | hsub
    · exact hd
    · exact (hij (Subtype.ext (hinj (Subset.antisymm hsub
        ((ht i).mp i.property j hsub))))).elim
    · exact (hij (Subtype.ext (hinj (Subset.antisymm
        ((ht j).mp j.property i hsub) hsub)))).elim
  refine ⟨t,hdis,hcover,?_,?_,?_⟩
  · apply Subset.antisymm
    · rintro x hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨j,hj⟩
    · rintro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      obtain ⟨j,hij⟩ := hcover i
      exact mem_iUnion.mpr ⟨j,hij hi⟩
  · apply Subset.antisymm
    · rintro x hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨j,hj⟩
    · rintro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      obtain ⟨j,hij⟩ := hcover i
      exact mem_iUnion.mpr ⟨j,interior_mono hij hi⟩
  · intro i hi
    obtain ⟨j,hij⟩ := hcover i
    refine ⟨j,subset_interior_of_subset_of_disjoint_frontiers hij ?_⟩
    exact hfront (fun heq => hi (heq ▸ j.property))

end PoincareConjecture.M76
