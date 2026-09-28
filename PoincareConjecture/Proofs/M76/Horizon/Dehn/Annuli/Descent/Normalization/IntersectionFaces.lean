import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.FaceData
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartFaceImage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeEndpointImageFace
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineIntersectionRanks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension












set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K K₀ K₁ : SimplicialComplex ℝ V} {j : V → t.Carrier}
  {Q : OpenPartialHomeomorph t.Carrier E} {B : OpenPartialHomeomorph s.Carrier E}
  {J : SimplicialComplex ℝ E} {N : K.faces → Set t.Carrier} {R : Set M}

theorem RelativeFaceMotionData.exists_active_face_bound
    (motion : RelativeFaceMotionData step K K₀ K₁ j Q B J N R)
    (hK : K.faces.Finite) {face : Finset V} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    (hj : PolyhedralPLInCharts t.charts j K.space)
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid E)
    (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target) :
    ∃ L : SimplicialComplex ℝ E,
      L.faces.Finite ∧
      L.space = Q '' (j '' convexHull ℝ (face : Set V) ∩ Q.source) ∩ J.space ∧
      (∀ a ∈ L.faces, a.card ≤ face.card) ∧
      ∀ a ∈ motion.freeComplex.faces, a ∉ motion.fixedComplex.faces →
        convexHull ℝ (a : Set E) ⊆ L.space ∧ a.card ≤ face.card := by
  obtain ⟨L, hL, hLs, hbound⟩ := hj.exists_finite_face_chart_image K hK hface Q hQ J hJ hJQ
  have hcover : motion.freeComplex.space ⊆ motion.fixedComplex.space ∪ L.space := by
    intro z hz
    have hzsource : z ∈ Q '' (j '' K₁.space ∩ Q.source) ∩ J.space := by
      rw [← motion.source_space, ← motion.free_space]
      exact hz
    obtain ⟨⟨y, ⟨⟨x, hx, rfl⟩, hjxQ⟩, hvalue⟩, hzsupport⟩ := hzsource
    rcases hsucc.subset hx with hxold | hxactive
    · left
      rw [motion.fixed_space, motion.protected_space]
      exact ⟨⟨j x, ⟨mem_image_of_mem j hxold, hjxQ⟩, hvalue⟩, hzsupport⟩
    · right
      rw [hLs]
      exact ⟨⟨j x, ⟨mem_image_of_mem j hxactive, hjxQ⟩, hvalue⟩, hzsupport⟩
  refine ⟨L, hL, hLs, hbound, ?_⟩
  intro a ha hnot
  have hsub := motion.freeComplex.free_face_hull_subset_closed_active
    motion.fixedComplex motion.fixed_le (L.isCompact_space_of_finite hL).isClosed
    hcover ha hnot
  exact ⟨hsub, motion.freeComplex.face_card_le_of_hull_subset_finite_carrier
    L hL ha hsub hbound⟩

omit [FiniteDimensional ℝ V] in
theorem RelativeFaceMotionData.targets_space_of_prefix_agreement
    (motion : RelativeFaceMotionData step K K₀ K₁ j Q B J N R)
    {jfinal : V → t.Carrier} (heq : EqOn jfinal j K₀.space) (a : K₀.faces) :
    (motion.targets a).space = B '' (((step.projection ∘ step.inclusion) ∘ jfinal) ''
      convexHull ℝ (a.val : Set V) ∩ B.source) ∩ J.space := by
  have himage : ((step.projection ∘ step.inclusion) ∘ jfinal) ''
      convexHull ℝ (a.val : Set V) =
      ((step.projection ∘ step.inclusion) ∘ j) '' convexHull ℝ (a.val : Set V) :=
    image_congr (fun x hx ↦ congrArg (step.projection ∘ step.inclusion)
      (heq (K₀.convexHull_subset_space a.property hx)))
  rw [himage]
  exact motion.targets_space a

omit [FiniteDimensional ℝ V] in
theorem RelativeFaceMotionData.coordinate_of_successor_agreement
    (motion : RelativeFaceMotionData step K K₀ K₁ j Q B J N R)
    (hJQ : J.space ⊆ Q.target) {jfinal : V → t.Carrier}
    (heq : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    {x : V} (hx : x ∈ K₁.space) (hxQ : j x ∈ Q.source) (hxJ : Q (j x) ∈ J.space) :
    Q (jfinal x) = motion.coordinates.map 1 (Q (j x)) := by
  have hinside : motion.coordinates.map 1 (Q (j x)) ∈ J.space :=
    (motion.coordinates.carrier 1).subset
      (mem_image_of_mem (motion.coordinates.map 1) hxJ)
  rw [heq hx]
  change Q (motion.ambient 1 (j x)) = motion.coordinates.map 1 (Q (j x))
  rw [motion.chart_formula 1 hxQ]
  exact Q.right_inv (hJQ hinside)

omit [FiniteDimensional ℝ V] in


theorem RelativeFaceMotionData.exists_position_faces_at_intersection
    (motion : RelativeFaceMotionData step K K₀ K₁ j Q B J N R)
    (old : K₀.faces) {w : E}
    (hsource : w ∈ motion.coordinates.map 1 '' motion.source.space)
    (hfree : w ∉ motion.protectedSource.space)
    (htarget : w ∈ (motion.targets old).space) :
    ∃ a b : Finset E,
      a ∈ motion.freeComplex.faces ∧ a ∉ motion.fixedComplex.faces ∧
      b ∈ (motion.targets old).faces ∧
      w ∈ intrinsicInterior ℝ (convexHull ℝ (motion.coordinates.map 1 '' (a : Set E))) ∧
      w ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set E)) ∧
      affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E) ∪ (b : Set E)) = ⊤ ∧
      b.card ≤ old.val.card ∧
      Module.finrank ℝ ((affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E)) ⊓
        affineSpan ℝ (b : Set E)).direction) + Module.finrank ℝ E =
        (a.card - 1) + (b.card - 1) := by
  have hfinite : motion.freeComplex.faces.Finite :=
    motion.subdivision_finite.subset motion.free_le
  have haff : motion.freeComplex.AffineOnFaces (motion.coordinates.map 1) :=
    fun a ha ↦ motion.endpoint_affine a (motion.free_le ha)
  have hfix : EqOn (motion.coordinates.map 1) id motion.fixedComplex.space :=
    fun z hz ↦ motion.coordinates.fixed_protected 1 z (motion.fixed_space.subset hz)
  have hwimage : w ∈ motion.coordinates.map 1 '' motion.freeComplex.space := by
    rw [motion.free_space]
    exact hsource
  have hwfree : w ∉ motion.fixedComplex.space := fun hw ↦ hfree (motion.fixed_space.subset hw)
  obtain ⟨a, ha, ha0, hwa, aimage, haimage, hcard, hind⟩ :=
    SimplicialComplex.AffineOnFaces.exists_free_endpoint_image_face hfinite haff
      (motion.coordinates.map 1).injective.injOn motion.fixedComplex hfix hwimage hwfree
  obtain ⟨b, hb, hwb⟩ := (motion.targets old).exists_face_intrinsicInterior_of_finite
    (motion.targets_finite old) htarget
  have hspan : affineSpan ℝ
      (motion.coordinates.map 1 '' (a : Set E) ∪ (b : Set E)) = ⊤ := by
    rcases motion.position old a ha ha0 b hb with hspan | hdis
    · exact hspan
    · exact False.elim (disjoint_left.mp hdis hwa (intrinsicInterior_subset hwb))
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
      affineSpan ℝ (b : Set E) = ⊤ := by
    rw [← AffineSubspace.span_union]
    exact hspan
  have hrank := AffineSubspace.finrank_inf_add_finrank_sup_of_mem
    (affineSpan ℝ (motion.coordinates.map 1 '' (a : Set E))) (affineSpan ℝ (b : Set E))
    (convexHull_subset_affineSpan (s := motion.coordinates.map 1 '' (a : Set E))
      (intrinsicInterior_subset hwa))
    (convexHull_subset_affineSpan (s := (b : Set E)) (intrinsicInterior_subset hwb))
  rw [hjoin, harank, hbrank] at hrank
  rw [AffineSubspace.direction_top, finrank_top] at hrank
  exact ⟨a, b, ha, ha0, hb, hwa, hwb, hspan, motion.targets_card old b hb, hrank⟩

end Geometry.OriginalPLTower
