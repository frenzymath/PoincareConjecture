import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.ModelComponents



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

theorem connectedComponentIn_eq_of_disjoint_closed_partition
    {X : Type*} [TopologicalSpace X] {S T F : Set X}
    (hS : IsClosed S) (hT : IsClosed T) (hdis : Disjoint S T)
    (hF : F = S ∪ T) {x : X} (hx : x ∈ S) :
    connectedComponentIn S x = connectedComponentIn F x := by
  have hSF : S ⊆ F := hF.symm ▸ subset_union_left
  have hcompl : ((Subtype.val : F → X) ⁻¹' S)ᶜ =
      (Subtype.val : F → X) ⁻¹' T := by
    ext y
    have hy := hF.subset y.property
    exact ⟨fun h => hy.resolve_left h, fun hT hS => disjoint_left.mp hdis hS hT⟩
  have hclopen : IsClopen ((Subtype.val : F → X) ⁻¹' S) :=
    ⟨hS.preimage continuous_subtype_val,
      isClosed_compl_iff.mp (hcompl ▸ hT.preimage continuous_subtype_val)⟩
  have hsub : connectedComponentIn F x ⊆ S := by
    rw [connectedComponentIn_eq_image (hSF hx)]
    rintro y ⟨z, hz, rfl⟩
    exact isPreconnected_connectedComponent.subset_isClopen hclopen
      ⟨⟨x, hSF hx⟩, mem_connectedComponent, hx⟩ hz
  exact (connectedComponentIn_mono x hSF).antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (hSF hx)) hsub)

open Classical in
theorem exists_whole_source_component_of_finite_model
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X] (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {S : Set X} (H : K.space ≃ₜ S)
    (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃ (T : Set X) (G : (K.edgeComponentComplex D).space ≃ₜ T),
      T ⊆ S ∧ (∀ x ∈ T, connectedComponentIn S x = T) ∧
      ∀ z, (G z : X) = (H (Set.inclusion
        (SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D)) z) : X) := by
  classical
  let P := K.edgeComponentComplex D
  have hPK : P.space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D)
  let j : P.space → X := fun z => H (Set.inclusion hPK z)
  have hj : IsEmbedding j :=
    IsEmbedding.subtypeVal.comp (H.isEmbedding.comp (IsEmbedding.inclusion hPK))
  let T := Set.range j
  let G : P.space ≃ₜ T := hj.toHomeomorph
  obtain ⟨z, hz⟩ := (K.edgeComponentComplex_isPathConnected D).nonempty
  let zK : K.space := ⟨z, hPK hz⟩
  have hP : (Subtype.val : K.space → E) ⁻¹' P.space = connectedComponent zK := by
    rw [← HamiltonIntervalTorus.edgeComponentComplex_connectedComponentIn K hK D hz,
      connectedComponentIn_eq_image (hPK hz)]
    exact preimage_image_eq _ Subtype.val_injective
  have hH : H '' connectedComponent zK = connectedComponent (H zK) := by
    simpa only [connectedComponentIn_univ, image_univ, H.surjective.range_eq] using
      H.image_connectedComponentIn (mem_univ zK)
  have hT : T = connectedComponentIn S (H zK : X) := by
    rw [connectedComponentIn_eq_image (H zK).property, ← hH, ← hP]
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨H (Set.inclusion hPK w), ⟨Set.inclusion hPK w, w.property, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  refine ⟨T, G, ?_, ?_, fun _ => rfl⟩
  · rintro x ⟨w, rfl⟩
    exact (H (Set.inclusion hPK w)).property
  · intro x hx
    rw [hT] at hx ⊢
    exact (connectedComponentIn_eq hx).symm

end PoincareConjecture.M76
