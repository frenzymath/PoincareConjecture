import PoincareConjecture.Proofs.M76.Mathlib.RadialEmbeddingSpace

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

section General

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

def vertexAbstractComplex (K : SimplicialComplex 𝕜 E) : AbstractSimplicialComplex K.vertices where
  faces := {s | s.map (Function.Embedding.subtype _) ∈ K.faces}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.map_nonempty.mp (K.nonempty_of_mem_faces hs), ?_⟩
    intro t hts ht
    exact K.down_closed hs (Finset.map_subset_map.mpr hts) (Finset.map_nonempty.mpr ht)
  singleton_mem v := by
    change ({v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
    rw [Finset.map_singleton]
    exact v.property

theorem faces_eq_vertexAbstractComplex_images (K : SimplicialComplex 𝕜 E) :
    K.faces = {t : Finset E | ∃ s ∈ K.vertexAbstractComplex.faces,
      (t : Set E) = Subtype.val '' (s : Set K.vertices)} := by
  classical
  ext t
  constructor
  · intro ht
    have hv : ∀ x ∈ t, x ∈ K.vertices := by
      intro x hx
      rw [vertices_eq]
      exact mem_iUnion₂.mpr ⟨t, ht, hx⟩
    have he := Finset.subtype_map_of_mem hv
    refine ⟨t.subtype (fun x => x ∈ K.vertices), ?_, ?_⟩
    · change (t.subtype (fun x => x ∈ K.vertices)).map (Function.Embedding.subtype _) ∈ K.faces
      rwa [he]
    · simpa only [Finset.coe_map, Function.Embedding.coe_subtype] using
        (congrArg (fun s : Finset E => (s : Set E)) he).symm
  · rintro ⟨s, hs, he⟩
    have heq : s.map (Function.Embedding.subtype _) = t := by
      apply Finset.coe_injective
      simpa only [Finset.coe_map, Function.Embedding.coe_subtype] using he.symm
    change s.map (Function.Embedding.subtype _) ∈ K.faces at hs
    rwa [heq] at hs

theorem finite_vertexAbstractComplex_faces {K : SimplicialComplex 𝕜 E}
    (hK : K.faces.Finite) : K.vertexAbstractComplex.faces.Finite :=
  Set.Finite.preimage (Finset.map_injective (Function.Embedding.subtype _)).injOn hK

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isRadialEmbedding_vertex_inclusion (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    K.vertexAbstractComplex.IsRadialEmbedding ((↑) : K.vertices → E) :=
  ⟨Subtype.val_injective, K, K.faces_eq_vertexAbstractComplex_images, hlin, hinj⟩

variable [DecidableEq E]

theorem isRadialEmbedding_link_vertex_inclusion (K : SimplicialComplex ℝ E) :
    (K.link 0).vertexAbstractComplex.IsRadialEmbedding ((↑) : (K.link 0).vertices → E) :=
  (K.link 0).isRadialEmbedding_vertex_inclusion
    (fun _ hs => linearIndependent_of_mem_link_zero hs) (injOn_normalize_link K)

end Geometry.SimplicialComplex
