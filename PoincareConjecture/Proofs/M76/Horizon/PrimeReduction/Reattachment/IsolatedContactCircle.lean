import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreComponentCount








set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem HasDisjointPolygonPresentation.exists_polygon_of_isolated_connected_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S C : Set E} (hS : HasDisjointPolygonPresentation S)
    (hCS : C ⊆ S) (hC : IsConnected C) (hclosed : IsClosed C)
    (hrest : IsClosed (S \ C)) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ P.boundary ℝ = C := by
  obtain ⟨m,k,P,hP,hcover,hdis⟩ := hS
  have hconn (i : Fin m) : IsConnected ((P i).boundary ℝ) := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hP i).2 (hP i).1
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  obtain ⟨x,hx⟩ := hC.nonempty
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover.subset (hCS hx))
  have hcomponent := Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover
    (fun i => (P i).boundary ℝ) (fun i => (P i).isClosed_boundary)
    (fun i => (hconn i).isPreconnected) hdis hcover.symm hj
  have hCP : C ⊆ (P j).boundary ℝ :=
    hcomponent ▸ hC.isPreconnected.subset_connectedComponentIn hx hCS
  have hPS : (P j).boundary ℝ ⊆ S := fun _ hz =>
    hcover.symm.subset (mem_iUnion_of_mem j hz)
  have hPC : (P j).boundary ℝ ⊆ C := by
    have hside := isPreconnected_iff_subset_of_disjoint_closed.mp
      (hconn j).isPreconnected C (S \ C) hclosed hrest
      (fun z hz => by
        by_cases hzC : z ∈ C
        · exact Or.inl hzC
        · exact Or.inr ⟨hPS hz,hzC⟩)
      (by simp only [inter_sdiff_self,inter_empty])
    exact hside.resolve_right (fun h => (h hj).2 hx)
  exact ⟨k j,P j,(hP j).1,(hP j).2,Subset.antisymm hPC hCP⟩

end PoincareConjecture.M76
