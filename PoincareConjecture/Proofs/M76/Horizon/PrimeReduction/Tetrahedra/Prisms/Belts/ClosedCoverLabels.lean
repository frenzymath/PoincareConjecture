import Mathlib.Topology.Connected.Basic



set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt

theorem eq_labels_of_connected_finite_closed_cover
    {X ι α : Type*} [TopologicalSpace X] [Finite ι]
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i)) (hne : ∀ i, (C i).Nonempty)
    (hconn : IsPreconnected (⋃ i, C i))
    (label : ι → α)
    (hcontact : ∀ i j, (C i ∩ C j).Nonempty → label i = label j) :
    ∀ i j, label i = label j := by
  classical
  intro i j
  by_contra hij
  let P := ⋃ k : {k // label k = label i}, C k
  let Q := ⋃ k : {k // label k ≠ label i}, C k
  have hP : IsClosed P := isClosed_iUnion_of_finite (fun k : {k // label k = label i} => hC k)
  have hQ : IsClosed Q := isClosed_iUnion_of_finite (fun k : {k // label k ≠ label i} => hC k)
  have hcover : (⋃ k, C k) ⊆ P ∪ Q := by
    intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx
    by_cases heq : label k = label i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k,heq⟩,hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k,heq⟩,hk⟩)
  obtain ⟨x,hxi⟩ := hne i
  obtain ⟨y,hyj⟩ := hne j
  obtain ⟨z,_,hzP,hzQ⟩ := isPreconnected_closed_iff.mp hconn P Q hP hQ hcover
    ⟨x,mem_iUnion.mpr ⟨i,hxi⟩,mem_iUnion.mpr ⟨⟨i,rfl⟩,hxi⟩⟩
    ⟨y,mem_iUnion.mpr ⟨j,hyj⟩,mem_iUnion.mpr ⟨⟨j,Ne.symm hij⟩,hyj⟩⟩
  obtain ⟨k,hk⟩ := mem_iUnion.mp hzP
  obtain ⟨l,hl⟩ := mem_iUnion.mp hzQ
  exact l.2 ((hcontact k l ⟨z,hk,hl⟩).symm.trans k.2)

end PoincareConjecture.M76.PrismBelt
