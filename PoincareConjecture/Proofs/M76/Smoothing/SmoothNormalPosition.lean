import PoincareConjecture.Proofs.M76.Mathlib.FiniteSmoothLeafField
import PoincareConjecture.Proofs.M76.Smoothing.PositiveFacePlanes
import PoincareConjecture.Proofs.M76.Mathlib.BrouwerStarProjection

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

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

end PoincareConjecture.M76.Smoothing
