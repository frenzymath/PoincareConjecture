import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FaceLinkProjection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineNormalIndependence

/-!
# The normal link of an actual geometric face star

The actual orthogonal normal projection of a closed face star in
general position is the cone on its independently realized face link.
See Cairns 1940, Section 4, p. 800, and M76 derivation 37.
-/

set_option autoImplicit false

open Set AbstractSimplicialComplex

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Affine orthogonal projection to the normal space of a plane
through the specified center. See Cairns p. 800 and M76 derivation 37. -/
noncomputable def normalAffineProjection (L : Submodule ℝ E) (p : E) : E →ᵃ[ℝ] ↥(Lᗮ) :=
  Lᗮ.orthogonalProjectionOnto.toLinearMap.toAffineMap.comp
    (AffineEquiv.vaddConst ℝ p).symm.toAffineMap

/-- The normal affine projection acts on the displacement from its
center. See Cairns p. 800 and M76 derivation 37. -/
theorem normalAffineProjection_apply (L : Submodule ℝ E) (p x : E) :
    L.normalAffineProjection p x = Lᗮ.orthogonalProjectionOnto (x - p) := rfl

/-- Every point of the centered tangent plane has zero normal
projection. See Cairns p. 800 and M76 derivation 37. -/
theorem normalAffineProjection_eq_zero (L : Submodule ℝ E) (p : E) {x : E}
    (hx : x - p ∈ L) : L.normalAffineProjection p x = 0 :=
  L.orthogonalProjectionOnto_orthogonal_apply_eq_zero hx

end Submodule

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- In general position, the projected vertices of the actual face
link are linearly independent in the normal space.
See Cairns pp. 799--800 and M76 derivation 37. -/
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

/-- The normal projection of the actual link gives a faithful
independent radial realization on its actual vertex labels.
See Cairns p. 800 and M76 derivation 37. -/
noncomputable def faceNormalRadialEmbedding (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E)) :
    (K.faceLink s).vertexAbstractComplex.RadialEmbedding
      ↥((affineSpan ℝ (s : Set E)).directionᗮ) :=
  ⟨_, (K.faceLink s).vertexAbstractComplex.isRadialEmbedding_of_linearIndependent
    (K.linearIndependent_faceLink_normal hv hs hp)⟩

/-- The normal image of the original closed face star is exactly
the conical carrier of its actual normal link, including empty links.
See Cairns Section 4, p. 800, and M76 derivation 37. -/
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
