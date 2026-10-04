import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFaceMotionData
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FreeEndpointImageFace
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Affine.Mathlib.AffineIntersectionRanks
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.FaceLinkDimension

/-!
# Actual faces and the exact rank equation at a free intersection

The actual endpoint image selects an unchanged free source face.
The actual old comparison complex selects its target face. At their
common point the retained position alternative forces the full affine
join, so the nonempty-intersection rank equation applies literally.
See Hudson1969, Lemma4.6, and Dehn032, sections6--7.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- An actual free point common to the endpoint source and an old
comparison image produces two actual intrinsic-interior faces, the
full affine join and its exact nonempty-intersection rank equation.
No dimension is assigned to an empty intersection and no source
refinement changes the retained position alternatives.
See Dehn032, sections6--7. -/
theorem FaceMotionData.exists_position_faces_at_intersection
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} {j : V2 → t.Carrier}
    {Q : OpenPartialHomeomorph t.Carrier V3}
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (old : K₀.faces) {w : V3}
    (hsource : w ∈ motion.coordinates.map 1 '' motion.source.space)
    (hfree : w ∉ motion.fixedSource.space)
    (htarget : w ∈ (motion.targets old).space) :
    ∃ a b : Finset V3,
      a ∈ motion.freeComplex.faces ∧ a ∉ motion.fixedComplex.faces ∧
      b ∈ (motion.targets old).faces ∧
      w ∈ intrinsicInterior ℝ
        (convexHull ℝ (motion.coordinates.map 1 '' (a : Set V3))) ∧
      w ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) ∧
      affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3) ∪ (b : Set V3)) =
        motion.plane ∧
      b.card ≤ old.val.card ∧
      Module.finrank ℝ ((affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3)) ⊓
        affineSpan ℝ (b : Set V3)).direction) + Module.finrank ℝ motion.plane.direction =
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
      (motion.coordinates.map 1 '' (a : Set V3) ∪ (b : Set V3)) = motion.plane := by
    rcases motion.position old a ha ha0 b hb with hspan | hdis
    · exact hspan
    · exact False.elim (Set.disjoint_left.mp hdis hwa (intrinsicInterior_subset hwb))
  have hacard : a.card = (a.card - 1) + 1 := by
    have hpos := Finset.card_pos.mpr (motion.freeComplex.nonempty_of_mem_faces ha)
    omega
  have hbcard : b.card = (b.card - 1) + 1 := by
    have hpos := Finset.card_pos.mpr ((motion.targets old).nonempty_of_mem_faces hb)
    omega
  have hrange : range ((↑) : aimage → V3) =
      motion.coordinates.map 1 '' (a : Set V3) := Subtype.range_coe.trans haimage
  have harank : Module.finrank ℝ
      (affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3))).direction = a.card - 1 := by
    rw [direction_affineSpan]
    have h := hind.finrank_vectorSpan (n := a.card - 1)
      (show Fintype.card aimage = (a.card - 1) + 1 by
        simpa only [Fintype.card_coe] using hcard.trans hacard)
    rw [hrange] at h
    exact h
  have hbrank : Module.finrank ℝ (affineSpan ℝ (b : Set V3)).direction = b.card - 1 :=
    (motion.targets old).finrank_faceDirection_of_card hb hbcard
  have hjoin : affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3)) ⊔
      affineSpan ℝ (b : Set V3) = motion.plane := by
    rw [← AffineSubspace.span_union]
    exact hspan
  have hrank := AffineSubspace.finrank_inf_add_finrank_sup_of_mem
    (affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3)))
    (affineSpan ℝ (b : Set V3))
      (convexHull_subset_affineSpan (s := motion.coordinates.map 1 '' (a : Set V3))
        (intrinsicInterior_subset hwa))
      (convexHull_subset_affineSpan (s := (b : Set V3)) (intrinsicInterior_subset hwb))
  rw [hjoin, harank, hbrank] at hrank
  exact ⟨a, b, ha, ha0, hb, hwa, hwb, hspan, motion.targets_card old b hb, hrank⟩

end Geometry.OriginalPLTower
