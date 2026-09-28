import PoincareConjecture.Proofs.Horizon.Topology.Connected.FiniteComplement
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

open Set

namespace Poincare.Topology

theorem exists_component_representative_of_closure_cover
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {S : Set X} (hS : IsOpen S) (R : Finset X)
    (hcover : (⋃ y ∈ R, closure (connectedComponentIn S y)) = univ)
    {x : X} (hx : x ∈ S) :
    ∃ y ∈ R, connectedComponentIn S x = connectedComponentIn S y := by
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover.symm ▸ mem_univ x)
  obtain ⟨z, hzx, hzy⟩ := mem_closure_iff.mp hxy _ hS.connectedComponentIn
    (mem_connectedComponentIn hx)
  exact ⟨y, hy, (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm⟩

theorem exists_finite_component_closure_cover_of_dense
    {X : Type*} [TopologicalSpace X] {S : Set X}
    [Finite (ConnectedComponents S)] (hS : Dense S) :
    ∃ R : Finset X, (∀ x ∈ R, x ∈ S) ∧
      (∀ x ∈ R, ∀ y ∈ R, connectedComponentIn S x = connectedComponentIn S y → x = y) ∧
      (⋃ x ∈ R, closure (connectedComponentIn S x)) = univ := by
  classical
  choose a ha using (ConnectedComponents.surjective_coe :
    Function.Surjective (ConnectedComponents.mk : S → ConnectedComponents S))
  let R := (finite_range (fun q => (a q : X))).toFinset
  have hR (x : X) : x ∈ R ↔ ∃ q, (a q : X) = x := by
    simp only [R, Finite.mem_toFinset, mem_range]
  have hcover : (⋃ x ∈ R, connectedComponentIn S x) = S := by
    apply Subset.antisymm
    · exact iUnion₂_subset fun x _ => connectedComponentIn_subset S x
    · intro x hx
      let q := ConnectedComponents.mk (⟨x, hx⟩ : S)
      have hrep : ConnectedComponents.mk (a q) =
          ConnectedComponents.mk (⟨x, hx⟩ : S) := ha q
      refine mem_iUnion₂.mpr ⟨a q, (hR _).mpr ⟨q, rfl⟩, ?_⟩
      rw [connectedComponentIn_eq_image (a q).property]
      exact ⟨⟨x, hx⟩, ConnectedComponents.coe_eq_coe'.mp hrep.symm, rfl⟩
  refine ⟨R, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, rfl⟩ := (hR x).mp hx
    exact (a q).property
  · intro x hx y hy hxy
    obtain ⟨q, rfl⟩ := (hR x).mp hx
    obtain ⟨q', rfl⟩ := (hR y).mp hy
    have hcc : ConnectedComponents.mk (a q) = ConnectedComponents.mk (a q') := by
      rw [connectedComponentIn_eq_image (a q).property,
        connectedComponentIn_eq_image (a q').property,
        (image_injective.mpr Subtype.coe_injective).eq_iff] at hxy
      exact ConnectedComponents.coe_eq_coe.mpr hxy
    have hqq' : q = q' := (ha q).symm.trans (hcc.trans (ha q'))
    exact congrArg (fun q => (a q : X)) hqq'
  · rw [← R.closure_biUnion, hcover, hS.closure_eq]

theorem dense_compl_finite_frontier_union
    {X I : Type*} [TopologicalSpace X] (s : Finset I) (A : I → Set X)
    (hclosed : ∀ i ∈ s, IsClosed (A i)) :
    Dense (⋃ i ∈ s, frontier (A i))ᶜ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have heq : (⋃ j ∈ insert i s, frontier (A j)) =
          frontier (A i) ∪ ⋃ j ∈ s, frontier (A j) := by simp
      rw [heq, compl_union]
      exact (interior_eq_empty_iff_dense_compl.mp
        (interior_frontier (hclosed i (Finset.mem_insert_self _ _)))).inter_of_isOpen_left
          (ih (fun j hj => hclosed j (Finset.mem_insert_of_mem hj)))
          isClosed_frontier.isOpen_compl

end Poincare.Topology
