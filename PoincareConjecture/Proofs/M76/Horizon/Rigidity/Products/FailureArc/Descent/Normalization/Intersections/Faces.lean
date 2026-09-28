import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FaceData
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeEndpointImageFace
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineIntersectionRanks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem MarkedSurfaceMotionData.exists_position_faces_at_intersection
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} {j : V → t.Carrier}
    {Q : OpenPartialHomeomorph t.Carrier E}
    {B : OpenPartialHomeomorph s.Carrier E} {J : SimplicialComplex ℝ E}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (old : K₀.faces) {w : E}
    (hsource : w ∈ motion.coordinates.map 1 '' motion.source.space)
    (hfree : w ∉ motion.fixedSource.space)
    (htarget : w ∈ (motion.targets old).space) :
    ∃ a b : Finset E,
      a ∈ motion.freeComplex.faces ∧ a ∉ motion.fixedComplex.faces ∧
      b ∈ (motion.targets old).faces ∧
      w ∈ intrinsicInterior ℝ
        (convexHull ℝ (motion.coordinates.map 1 '' (a : Set E))) ∧
      w ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set E)) ∧
      affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E) ∪ (b : Set E)) =
        motion.plane ∧
      b.card ≤ old.val.card ∧
      Module.finrank ℝ ((affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E)) ⊓
        affineSpan ℝ (b : Set E)).direction) + Module.finrank ℝ motion.plane.direction =
        (a.card - 1) + (b.card - 1) := by
  have hfinite : motion.freeComplex.faces.Finite :=
    motion.subdivision_finite.subset motion.free_le
  have haff : motion.freeComplex.AffineOnFaces (motion.coordinates.map 1) :=
    fun a ha => motion.endpoint_affine a (motion.free_le ha)
  have hfix : EqOn (motion.coordinates.map 1) id motion.fixedComplex.space :=
    fun z hz => motion.coordinates.fixed_protected 1 z (motion.fixed_space.subset hz)
  have hwimage : w ∈ motion.coordinates.map 1 '' motion.freeComplex.space := by
    rw [motion.free_space]
    exact hsource
  have hwfree : w ∉ motion.fixedComplex.space :=
    fun hw => hfree (motion.fixed_space.subset hw)
  obtain ⟨a, ha, ha0, hwa, aimage, haimage, hcard, hind⟩ :=
    SimplicialComplex.AffineOnFaces.exists_free_endpoint_image_face hfinite haff
      (motion.coordinates.map 1).injective.injOn motion.fixedComplex hfix hwimage hwfree
  obtain ⟨b, hb, hwb⟩ := (motion.targets old).exists_face_intrinsicInterior_of_finite
    (motion.targets_finite old) htarget
  have hspan : affineSpan ℝ
      (motion.coordinates.map 1 '' (a : Set E) ∪ (b : Set E)) = motion.plane := by
    rcases motion.position old a ha ha0 b hb with hspan | hdis
    · exact hspan
    · exact False.elim (Set.disjoint_left.mp hdis hwa (intrinsicInterior_subset hwb))
  have hacard : a.card = (a.card - 1) + 1 := by
    have hpos := Finset.card_pos.mpr (motion.freeComplex.nonempty_of_mem_faces ha)
    omega
  have hbcard : b.card = (b.card - 1) + 1 := by
    have hpos := Finset.card_pos.mpr ((motion.targets old).nonempty_of_mem_faces hb)
    omega
  have hrange : range ((↑) : aimage → E) =
      motion.coordinates.map 1 '' (a : Set E) := Subtype.range_coe.trans haimage
  have harank : Module.finrank ℝ
      (affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E))).direction = a.card - 1 := by
    rw [direction_affineSpan]
    have h := hind.finrank_vectorSpan (n := a.card - 1)
      (show Fintype.card aimage = (a.card - 1) + 1 by
        simpa only [Fintype.card_coe] using hcard.trans hacard)
    rw [hrange] at h
    exact h
  have hbrank : Module.finrank ℝ (affineSpan ℝ (b : Set E)).direction = b.card - 1 :=
    (motion.targets old).finrank_faceDirection_of_card hb hbcard
  have hjoin : affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E)) ⊔
      affineSpan ℝ (b : Set E) = motion.plane := by
    rw [← AffineSubspace.span_union]
    exact hspan
  have hrank := AffineSubspace.finrank_inf_add_finrank_sup_of_mem
    (affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E)))
    (affineSpan ℝ (b : Set E))
      (convexHull_subset_affineSpan (s := motion.coordinates.map 1 '' (a : Set E))
        (intrinsicInterior_subset hwa))
      (convexHull_subset_affineSpan (s := (b : Set E)) (intrinsicInterior_subset hwb))
  rw [hjoin, harank, hbrank] at hrank
  exact ⟨a, b, ha, ha0, hb, hwa, hwb, hspan, motion.targets_card old b hb, hrank⟩

end Geometry.OriginalPLTower
