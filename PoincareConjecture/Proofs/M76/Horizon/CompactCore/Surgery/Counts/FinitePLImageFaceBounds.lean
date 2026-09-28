import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds



set_option autoImplicit false

open Set Geometry

namespace Geometry

theorem FinitePiecewiseAffineOn.face_card_le_of_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {f : E → F} {K : SimplicialComplex ℝ E}
    (hf : FinitePiecewiseAffineOn f K.space) (hK : K.faces.Finite)
    {n : ℕ} (hbound : ∀ a ∈ K.faces, a.card ≤ n)
    (L : SimplicialComplex ℝ F) (himage : L.space ⊆ f '' K.space) :
    ∀ b ∈ L.faces, b.card ≤ n := by
  obtain ⟨J, hJ, hJs, hfJ⟩ := hf
  have hJbound : ∀ a ∈ J.faces, a.card ≤ n := by
    intro a ha
    exact J.face_card_le_of_hull_subset_finite_carrier K hK ha
      ((J.convexHull_subset_space ha).trans hJs.subset) hbound
  obtain ⟨I, hI, hIs, hfaces⟩ := hfJ.exists_finite_triangulation_image hJ
  have hIbound : ∀ a ∈ I.faces, a.card ≤ n := by
    intro a ha
    obtain ⟨b, hb, _, hab⟩ := hfaces a ha
    exact hab.trans (hJbound b hb)
  intro a ha
  apply L.face_card_le_of_hull_subset_finite_carrier I hI ha _ hIbound
  rw [hIs, hJs]
  exact (L.convexHull_subset_space ha).trans himage

end Geometry
