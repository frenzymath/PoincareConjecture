import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedSubcomplexCarriers

/-!
# The same protected subcomplex after an actual vertex motion

An endpoint fixes the entire protected carrier. Its actual embedded
image therefore contains the same protected faces, and the next
face-affine endpoint composes on the original triangulation.
See Hudson1969, Lemma4.5, and Dehn029, section3.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {J Q : SimplicialComplex ℝ E} {f g : E → E}

/-- A face-affine embedding fixing a whole subcomplex retains
its literal faces in the actual image complex. See Dehn029,
section3; no new protected carrier is chosen. -/
theorem AffineOnFaces.protected_le_embeddedImage
    (hf : J.AffineOnFaces f) (hinj : InjOn f J.space)
    (hQJ : Q ≤ J) (hfix : EqOn f id Q.space) :
    Q ≤ hf.embeddedImage hinj := by
  classical
  intro s hs
  change s ∈ (hf.embeddedImage hinj).faces
  rw [hf.embeddedImage_faces hinj]
  refine ⟨s, hQJ hs, ?_⟩
  calc
    s.image f = s.image id := by
      apply Finset.image_congr
      intro x hx
      exact hfix (Q.subset_space hs hx)
    _ = s := Finset.image_id

/-- A second face-affine map on the actual embedded image
composes on the original faces. See Dehn029, section3. -/
theorem AffineOnFaces.comp_on_embeddedImage
    (hf : J.AffineOnFaces f) (hinj : InjOn f J.space)
    (hg : (hf.embeddedImage hinj).AffineOnFaces g) :
    J.AffineOnFaces (g ∘ f) := by
  classical
  apply hf.comp_of_face_images hg
  intro s hs
  refine ⟨s.image f, ?_, ?_⟩
  · rw [hf.embeddedImage_faces hinj]
    exact mem_image_of_mem _ hs
  · rw [Finset.coe_image]

end Geometry.SimplicialComplex
