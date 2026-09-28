import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalComponentSubregions









set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.component_frontier_away_from_old_boundary
    {X ι ν : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q F : Set X}
    (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hfront : frontier Q = F ∪ ⋃ i, S i) {x : X} (hx : x ∈ Q)
    (haway : Disjoint (_root_.connectedComponentIn Q x) F) :
    IsCompact (_root_.connectedComponentIn Q x) ∧
      PLDomain e (_root_.connectedComponentIn Q x) ∧
      IsConnected (_root_.connectedComponentIn Q x) ∧
      frontier (_root_.connectedComponentIn Q x) =
        ⋃ i : {i : ν // S i ⊆ _root_.connectedComponentIn Q x}, S i := by
  classical
  have hS (i) : IsConnected (S i) := isConnected_iff_connectedSpace.mpr
    ((sS i).parametrization.connectedSpace_iff.mp (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by simp) (0 : V3) zero_le_one)))
  obtain ⟨_,D,owner,hD,hdis,_,howner,hsep,hactual⟩ :=
    exists_marked_pl_component_domains hQ hPL S hS
      (fun i => (subset_iUnion S i).trans (subset_union_right.trans hfront.symm.subset))
  let c := ConnectedComponents.mk (⟨x,hx⟩ : Q)
  have hDc : D c = _root_.connectedComponentIn Q x := hactual ⟨x,hx⟩
  have hwhole (i) : S i ⊆ D c ∨ Disjoint (S i) (D c) := by
    by_cases hi : owner i = c
    · exact Or.inl ((howner i c).mpr hi)
    · exact Or.inr (hsep i c hi)
  have hboundary : frontier (D c) = ⋃ i : {i : ν // S i ⊆ D c}, S i := by
    rw [(hD c).2.2.2.2,hfront]
    apply Subset.antisymm
    · rintro y ⟨hyD,hyF | hyS⟩
      · exact False.elim (disjoint_left.mp haway (hDc.subset hyD) hyF)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hyS
        rcases hwhole i with hsub | hmiss
        · exact mem_iUnion.mpr ⟨⟨i,hsub⟩,hi⟩
        · exact False.elim (disjoint_left.mp hmiss hi hyD)
    · intro y hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      exact ⟨i.property hi,Or.inr (mem_iUnion.mpr ⟨i,hi⟩)⟩
  rw [hDc] at hboundary
  exact ⟨hDc ▸ (hD c).1,hDc ▸ (hD c).2.1,hDc ▸ (hD c).2.2.1,hboundary⟩

end PoincareConjecture.M76
