import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X]

theorem edgeComponentComplex_connectedComponentIn
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {x : E} (hx : x ∈ (K.edgeComponentComplex D).space) :
    connectedComponentIn K.space x = (K.edgeComponentComplex D).space := by
  have hsub := SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D)
  obtain ⟨D', hD'⟩ := K.exists_edgeComponentComplex_of_isConnected hK
    (isConnected_connectedComponentIn_iff.mpr (hsub hx)) (connectedComponentIn_subset _ _)
  have hDD : D' = D := by
    by_contra hne
    exact disjoint_left.mp (K.pairwise_disjoint_edgeComponentComplex_space hne)
      (hD' (mem_connectedComponentIn (hsub hx))) hx
  subst D'
  exact hD'.antisymm ((K.edgeComponentComplex_isPathConnected D).isConnected.isPreconnected.subset_connectedComponentIn hx hsub)

theorem exists_source_component_of_model
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {S : Set X}
    (H : K.space ≃ₜ S) (F : X → E) (hF : Continuous F)
    (hHF : ∀ x : S, (H.symm x : E) = F x)
    (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃ (T : Set X) (G : (K.edgeComponentComplex D).space ≃ₜ T),
      T ⊆ S ∧ (∀ x ∈ T, connectedComponentIn S x = T) ∧
      (∀ z, (G z : X) = (H (Set.inclusion
        (SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D)) z) : X)) ∧
      ∀ x : T, (G.symm x : E) = F x := by
  let P := K.edgeComponentComplex D
  have hPK : P.space ⊆ K.space := SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D)
  let T : Set X := S ∩ F ⁻¹' P.space
  let G : P.space ≃ₜ T :=
    { toFun := fun z => ⟨H (Set.inclusion hPK z), (H (Set.inclusion hPK z)).property, by
        change F (H (Set.inclusion hPK z)) ∈ P.space
        rw [← hHF, H.symm_apply_apply]
        exact z.property⟩
      invFun := fun x => ⟨F x, x.property.2⟩
      left_inv := fun z => by
        apply Subtype.ext
        change F (H (Set.inclusion hPK z)) = z
        rw [← hHF, H.symm_apply_apply]
      right_inv := fun x => by
        apply Subtype.ext
        have hx : Set.inclusion hPK (⟨F x, x.property.2⟩ : P.space) =
            H.symm ⟨x, x.property.1⟩ := Subtype.ext (hHF ⟨x, x.property.1⟩).symm
        change (H (Set.inclusion hPK ⟨F x, x.property.2⟩) : X) = x
        rw [hx, H.apply_symm_apply]
      continuous_toFun := by fun_prop
      continuous_invFun := (hF.comp continuous_subtype_val).subtype_mk _ }
  have hTpre : IsPreconnected T := by
    let : PathConnectedSpace P.space :=
      isPathConnected_iff_pathConnectedSpace.mp (K.edgeComponentComplex_isPathConnected D)
    have hr : range (fun z : P.space => (G z : X)) = T := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (G z).property
      · intro hx
        exact ⟨G.symm ⟨x, hx⟩, congrArg Subtype.val (G.apply_symm_apply ⟨x, hx⟩)⟩
    rw [← hr]
    exact isPreconnected_range (continuous_subtype_val.comp G.continuous)
  have hFS : F '' S = K.space := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hHF ⟨x, hx⟩]
      exact (H.symm ⟨x, hx⟩).property
    · intro hz
      exact ⟨H ⟨z, hz⟩, (H ⟨z, hz⟩).property, by rw [← hHF, H.symm_apply_apply]⟩
  refine ⟨T, G, inter_subset_left, ?_, fun _ => rfl, fun _ => rfl⟩
  intro x hx
  apply Subset.antisymm
  · intro y hy
    refine ⟨connectedComponentIn_subset S x hy, ?_⟩
    have hmap := hF.continuousOn.image_connectedComponentIn_subset hx.1
    rw [hFS, edgeComponentComplex_connectedComponentIn K hK D hx.2] at hmap
    exact hmap (mem_image_of_mem F hy)
  · exact hTpre.subset_connectedComponentIn hx inter_subset_left

end PoincareConjecture.M76.HamiltonIntervalTorus
