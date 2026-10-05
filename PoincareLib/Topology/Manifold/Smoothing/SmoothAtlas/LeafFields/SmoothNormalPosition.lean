import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.LeafFields.FiniteSmoothLeafField
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Simplicial.PositiveFacePlanes
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.BrouwerStarProjection

/-!
# Smooth normal fields near finite three-dimensional complexes

The finite leaf-field recurrence uses actual positive-face plane
spaces and preserves smoothness on an ambient open neighborhood.
Purity and the initial vertex planes remain explicit. See Cairns
1940, pp. 803--805, 807 and M76 derivation 65.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- A finite pure three-complex with the closed-manifold link
incidence conditions and nonempty vertex targets admits a smooth
ambient transverse leaf field. See Cairns pp. 803--805, 807 and
M76 derivation 65. -/
theorem exists_smooth_transverse_leafField (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hedges : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    (hvertices : ∀ s ∈ K.faces, s.card = 1 →
      Nonempty (SecantTransversePlaneSpace 3 (K.closedFaceStar s).space)) :
    ∃ U : Set E, IsOpen U ∧ K.space ⊆ U ∧
      ∃ P : E → EuclideanSubspace E, EuclideanSubspace.IsSmoothLeafFieldOn P U ∧
        (∀ x ∈ U, Module.finrank ℝ (P x).subspace + 3 = Module.finrank ℝ E) ∧
        ∀ s ∈ K.faces, ∀ x ∈ convexHull ℝ (s : Set E),
          (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
  have hbound : ∀ s ∈ K.faces, s.card ≤ 4 := by
    intro s hs
    obtain ⟨t, _, hst, hcard⟩ := hpure s hs
    exact hcard ▸ Finset.card_le_card hst
  exact K.exists_smoothLeafField_near_space hfinite 3 hpure hvertices
    (fun _ hs hpos => contractible_positiveFaceStarPlanes K hK hfinite hbound
      hedges htriangles hs hpos)

/-- Full-dimensional simplexwise affine Brouwer vertex stars
supply the initial planes for the smooth leaf-field construction.
See Cairns pp. 799, 803--805, 807 and M76 derivation 65. -/
theorem exists_smooth_transverse_leafField_of_brouwerStars (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hedges : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    (hbrouwer : ∀ p : E, {p} ∈ K.faces →
      ∃ f : E → EuclideanSpace ℝ (Fin 3),
        (K.closedFaceStar {p}).AffineOnFaces f ∧
        InjOn f (K.closedFaceStar {p}).space ∧
        (interior (f '' (K.closedFaceStar {p}).space)).Nonempty) :
    ∃ U : Set E, IsOpen U ∧ K.space ⊆ U ∧
      ∃ P : E → EuclideanSubspace E, EuclideanSubspace.IsSmoothLeafFieldOn P U ∧
        (∀ x ∈ U, Module.finrank ℝ (P x).subspace + 3 = Module.finrank ℝ E) ∧
        ∀ s ∈ K.faces, ∀ x ∈ convexHull ℝ (s : Set E),
          (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
  apply exists_smooth_transverse_leafField K hK hfinite hpure hedges htriangles
  intro s hs hcard
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
  obtain ⟨f, hf, hinj, hfull⟩ := hbrouwer p hs
  simpa using K.nonempty_vertexStarPlanes_of_affineOnFaces hK hs f hf hinj hfull

end PoincareMT.M76.Smoothing
