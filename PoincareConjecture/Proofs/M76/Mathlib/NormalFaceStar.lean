import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection
import PoincareConjecture.Proofs.M76.Mathlib.AffineNormalIndependence









set_option autoImplicit false

open Set AbstractSimplicialComplex

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]



noncomputable def normalAffineProjection (L : Submodule ℝ E) (p : E) : E →ᵃ[ℝ] ↥(Lᗮ) :=
  Lᗮ.orthogonalProjectionOnto.toLinearMap.toAffineMap.comp
    (AffineEquiv.vaddConst ℝ p).symm.toAffineMap



theorem normalAffineProjection_apply (L : Submodule ℝ E) (p x : E) :
    L.normalAffineProjection p x = Lᗮ.orthogonalProjectionOnto (x - p) := rfl



theorem normalAffineProjection_eq_zero (L : Submodule ℝ E) (p : E) {x : E}
    (hx : x - p ∈ L) : L.normalAffineProjection p x = 0 :=
  L.orthogonalProjectionOnto_orthogonal_apply_eq_zero hx

end Submodule

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]




theorem linearIndependent_faceLink_normal (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E)) :
    LinearIndependent ℝ (fun v : (K.faceLink s).vertices =>
      (affineSpan ℝ (s : Set E)).direction.normalAffineProjection p v) := by
  let central : Set K.vertices := {v | v.val ∈ s}
  have hsvertices : (s : Set E) ⊆ K.vertices := by
    intro x hx
    rw [vertices_eq]
    exact mem_iUnion₂.mpr ⟨s, hs, hx⟩
  have hcentral : ((↑) : K.vertices → E) '' central = (s : Set E) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, hsvertices hx⟩, hx, rfl⟩
  have hcne : central.Nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces hs
    exact ⟨⟨x, hsvertices hx⟩, hx⟩
  have hp' : p ∈ affineSpan ℝ (((↑) : K.vertices → E) '' central) := by
    rwa [hcentral]
  have hnormal := hv.linearIndependent_orthogonal_normal hcne hp'
  rw [hcentral] at hnormal
  let outer : (K.faceLink s).vertices → {v : K.vertices // v ∉ central} :=
    fun v => ⟨⟨v.val, (K.faceLink_vertices_subset s v.property).1⟩,
      (K.faceLink_vertices_subset s v.property).2⟩
  have houter : Function.Injective outer := by
    intro v w hvw
    exact Subtype.ext (congrArg
      (fun z : {v : K.vertices // v ∉ central} => z.val.val) hvw)
  exact hnormal.comp outer houter




noncomputable def faceNormalRadialEmbedding (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E)) :
    (K.faceLink s).vertexAbstractComplex.RadialEmbedding
      ↥((affineSpan ℝ (s : Set E)).directionᗮ) :=
  ⟨_, (K.faceLink s).vertexAbstractComplex.isRadialEmbedding_of_linearIndependent
    (K.linearIndependent_faceLink_normal hv hs hp)⟩




theorem normal_image_closedFaceStar (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E)) :
    (affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
      (K.closedFaceStar s).space =
        (RadialEmbedding.cone (K.faceNormalRadialEmbedding hv hs hp)).space := by
  apply K.affine_image_closedFaceStar_eq_radialCone hs
  intro x hx
  exact Submodule.normalAffineProjection_eq_zero _ p
    ((affineSpan ℝ (s : Set E)).vsub_mem_direction (mem_affineSpan ℝ hx) hp)

end Geometry.SimplicialComplex
