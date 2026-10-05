import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Simplicial.FaceNormalExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplicialEmbeddedAffineImage

/-!
# The original face and edge in one ambient affine chart

The actual injective face-affine map constructs its image triangle
and marked edge. Their own plane coordinates extend to the ambient
chart while retaining both complete carriers. See PrimeReduction018,
sections1--2, and Kneser1929 p.254.
-/

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

open Classical in
/-- The original entire triangle and marked edge become the exact
standard planar triangle and unit edge at height zero. Coordinates
are constructed from their actual image vertices; no normal chart
is supplied. See PrimeReduction018, sections1--2. -/
theorem AffineOnFaces.exists_face_normal_coordinates
    {K : SimplicialComplex ℝ E} {f : E → F}
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    (h3 : Module.finrank ℝ F = 3) {s e : Finset E}
    (hs : s ∈ K.faces) (hsc : s.card = 3) (hec : e.card = 2) (hes : e ⊆ s) :
    ∃ T : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] F,
      T '' (convexHull ℝ (range rightTriangle) ×ˢ {(0 : ℝ)}) =
        f '' convexHull ℝ (s : Set E) ∧
      T '' (segment ℝ (0, 0) (1, 0) ×ˢ {(0 : ℝ)}) =
        f '' convexHull ℝ (e : Set E) ∧
      ∀ x ∈ convexHull ℝ (s : Set E), (T.symm (f x)).2 = 0 := by
  classical
  let J := hf.embeddedImage hi
  have he : e ∈ K.faces := K.down_closed hs hes (Finset.card_pos.mp (by omega))
  have hsJ : s.image f ∈ J.faces :=
    (hf.embeddedImage_faces hi).symm ▸ mem_image_of_mem (fun t : Finset E => t.image f) hs
  have hscJ : (s.image f).card = 3 :=
    (Finset.card_image_of_injOn (hi.mono (K.subset_space hs))).trans hsc
  have hecJ : (e.image f).card = 2 :=
    (Finset.card_image_of_injOn (hi.mono (K.subset_space he))).trans hec
  obtain ⟨a, r, hleft, _, hface, hedge, _, _, _⟩ :=
    exists_original_face_coordinates hsJ hscJ hecJ (Finset.image_subset_image hes)
  obtain ⟨T, hzero, _, hrange⟩ := a.exists_normal_extension hleft.injective h3
  have himage (C : Set (ℝ × ℝ)) : T '' (C ×ˢ {(0 : ℝ)}) = a '' C := by
    ext y
    constructor
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have ht0 : t = 0 := mem_singleton_iff.mp ht
      subst t
      exact ⟨z, hz, (hzero z).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z, 0), ⟨hz, rfl⟩, hzero z⟩
  have hfaceImage : convexHull ℝ (s.image f : Set F) =
      f '' convexHull ℝ (s : Set E) := by
    rw [Finset.coe_image]
    exact (hf.image_convexHull hs).symm
  have hedgeImage : convexHull ℝ (e.image f : Set F) =
      f '' convexHull ℝ (e : Set E) := by
    rw [Finset.coe_image]
    exact (hf.image_convexHull he).symm
  refine ⟨T, (himage _).trans (hface.trans hfaceImage),
    (himage _).trans (hedge.trans hedgeImage), ?_⟩
  intro x hx
  apply (hrange (f x)).mp
  have hm : f x ∈ a '' convexHull ℝ (range rightTriangle) :=
    (hface.trans hfaceImage).symm.subset ⟨x, hx, rfl⟩
  exact image_subset_range _ _ hm

end Geometry.SimplicialComplex
