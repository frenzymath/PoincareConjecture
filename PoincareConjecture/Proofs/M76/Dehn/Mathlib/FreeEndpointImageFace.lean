import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AffineOnFaces.exists_free_endpoint_image_face
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite)
    {f : E → E} (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    (P : SimplicialComplex ℝ E) (hfix : EqOn f id P.space)
    {w : E} (hw : w ∈ f '' K.space) (hnot : w ∉ P.space) :
    ∃ a : Finset E, a ∈ K.faces ∧ a ∉ P.faces ∧
      w ∈ intrinsicInterior ℝ (convexHull ℝ (f '' (a : Set E))) ∧
      ∃ b : Finset E, (b : Set E) = f '' (a : Set E) ∧ b.card = a.card ∧
        AffineIndependent ℝ ((↑) : b → E) := by
  classical
  let L := hf.embeddedImage hinj
  have hwL : w ∈ L.space := by
    rw [hf.embeddedImage_space hinj]
    exact hw
  obtain ⟨b, hb, hwb⟩ := L.exists_face_intrinsicInterior_of_finite
    (hf.embeddedImage_finite hinj hK) hwL
  have hbind := L.indep hb
  rw [hf.embeddedImage_faces hinj] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  have hwface : w ∈ intrinsicInterior ℝ (convexHull ℝ (f '' (a : Set E))) := by
    simpa only [Finset.coe_image] using hwb
  refine ⟨a, ha, ?_, hwface, a.image f, Finset.coe_image,
    Finset.card_image_iff.mpr (hinj.mono (K.subset_space ha)), hbind⟩
  intro haP
  have hwhull := intrinsicInterior_subset hwface
  rw [← hf.image_convexHull ha] at hwhull
  obtain ⟨x, hx, hfx⟩ := hwhull
  have hxP := P.convexHull_subset_space haP hx
  have hxw : x = w := (hfix hxP).symm.trans hfx
  exact hnot (hxw ▸ hxP)

end Geometry.SimplicialComplex
