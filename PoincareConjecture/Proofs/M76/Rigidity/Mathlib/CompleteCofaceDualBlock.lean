import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetBoundary









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem barycentricDualBlock_eq_of_cofaces_in_subcomplex
    (K L : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype L.faces]
    (hLK : L ≤ K) (s : Finset E)
    (hcofaces : ∀ t ∈ K.faces, s ⊆ t → t ∈ L.faces) :
    L.barycentricDualBlock s = K.barycentricDualBlock s := by
  classical
  apply le_antisymm (K.barycentricDualBlock_mono_of_subcomplex L hLK s)
  intro a ha
  obtain ⟨b, hb, hfaces, hchain, heq⟩ :=
    (K.barycentricSubdivision_faces_of_face_chains a).mp ha.1
  have hbf (v : Finset E) (hv : v ∈ b) : v ∈ L.faces := by
    have hcv : v.centroid ℝ id ∈ a :=
      heq.symm ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩
    obtain ⟨u, hu, hsu, hcent⟩ := ha.2 _ hcv
    have hueq : (⟨u, hu⟩ : K.faces) = ⟨v, hfaces v hv⟩ :=
      K.faceCentroid_injective hcent
    have huv : u = v := congrArg Subtype.val hueq
    exact hcofaces v (hfaces v hv) (huv ▸ hsu)
  refine ⟨(L.barycentricSubdivision_faces_of_face_chains a).mpr
    ⟨b, hb, hbf, hchain, heq⟩, ?_⟩
  intro x hx
  obtain ⟨u, hu, hsu, hux⟩ := ha.2 x hx
  exact ⟨u, hcofaces u hu hsu, hsu, hux⟩

end Geometry.SimplicialComplex
