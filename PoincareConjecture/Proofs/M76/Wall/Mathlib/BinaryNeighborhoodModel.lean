import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryDerivedEquivalence
import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryNeighborhoodImage

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem exists_binaryNeighborhood_model
    (A : SimplicialComplex ℝ E) (hAK : A ≤ K) :
    ∃ (h : E → ℝ) (f g : E → E) (e : K.space ≃ₜ K.space),
      K.AffineOnFaces h ∧
      (∀ v ∈ K.vertices, (v ∈ A.vertices → h v = 1) ∧
        (v ∉ A.vertices → h v = 0)) ∧
      MapsTo h K.space (Icc (0 : ℝ) 1) ∧
      K.barycentricSubdivision.AffineOnFaces f ∧
      (K.derivedSubdivision (fun s => s.val.binaryFaceCenter A.vertices)
        (K.positive_binary_face_centers A.vertices)).AffineOnFaces g ∧
      e.IsFinitePL ∧ e.symm.IsFinitePL ∧
      (∀ s : K.faces, f (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices) ∧
      (∀ x : K.space, (e x : E) = f x) ∧
      (∀ x : K.space, (e.symm x : E) = g x) ∧
      (∀ L : SimplicialComplex ℝ E, L ≤ K →
        f '' L.space = L.space ∧ g '' L.space = L.space) ∧
      EqOn f id A.space ∧
      f '' (K.barycentricNeighborhood A).space =
        K.space ∩ {x | (1 / 2 : ℝ) ≤ h x} ∧
      (∀ x : K.space, (x : E) ∈ (K.barycentricNeighborhood A).space ↔
        (1 / 2 : ℝ) ≤ h (e x)) := by
  obtain ⟨h, hh, hvalues, hbounds⟩ := K.exists_binary_face_height A.vertices
  obtain ⟨f, g, e, hf, hg, he, hei, hcenters, _, hval, hinv, hmarks, hfix⟩ :=
    K.exists_binaryDerived_homeomorph A hAK
  have himage := K.image_barycentricNeighborhood_binaryCenters A hf hcenters hh hvalues
  refine ⟨h, f, g, e, hh, hvalues, hbounds, hf, hg, he, hei,
    hcenters, hval, hinv, hmarks, hfix, himage, ?_⟩
  intro x
  constructor
  · intro hx
    have hmem := himage.subset ⟨x, hx, rfl⟩
    rw [hval x]
    exact hmem.2
  · intro hx
    obtain ⟨y, hy, heq⟩ := himage.superset ⟨(e x).property, hx⟩
    have hyK : y ∈ K.space := by
      have hyB := space_subset_of_le (K.barycentricNeighborhood_le A) hy
      exact K.barycentricSubdivision_isSubdivision.space_eq ▸ hyB
    have hey : e ⟨y, hyK⟩ = e x := Subtype.ext ((hval ⟨y, hyK⟩).trans heq)
    have hyx : y = (x : E) := congrArg Subtype.val (e.injective hey)
    rwa [hyx] at hy

end Geometry.SimplicialComplex
