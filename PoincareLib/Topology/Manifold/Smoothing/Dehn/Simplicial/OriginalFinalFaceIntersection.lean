import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFreeFaceBounds
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFaceComparisonTransport
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalPositionIntersectionFaces

/-!
# Actual final source points supply the retained intersection ranks

The active point lies outside the whole old prefix. Upper injectivity
and fixed coordinate protection keep its endpoint outside the complete
protected carrier. Whole-prefix and successor agreement identify the
actual final lower pair with the retained coordinate comparison.
Both source-face cardinality bounds are constructed from those images.
See Hudson1969, Lemma4.6, and Dehn032, sections4--7.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- A pair of actual final projected points, with the active point
outside the complete earlier prefix, supplies the retained two-face
comparison and exact rank equation. The motion and its images are the
particular witnesses already constructed in the finite history.
See Dehn032, sections4--7. -/
theorem FaceMotionData.exists_final_intersection_faces
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} (hK : K.faces.Finite) (hK₀ : K₀ ≤ K)
    {face : Finset V2} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V2))
    {j jfinal : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : InjOn j K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {B : OpenPartialHomeomorph s.Carrier V3}
    (hval : ∀ z, Q z = B (step.projection (step.inclusion z)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    {J : SimplicialComplex ℝ V3} {U : K.faces → Set t.Carrier}
    {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (hold : EqOn jfinal j K₀.space)
    (hnext : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    {x y : V2} (hx : x ∈ convexHull ℝ (face : Set V2)) (hxold : x ∉ K₀.space)
    (hxQ : j x ∈ Q.source)
    (old : K₀.faces) (hy : y ∈ convexHull ℝ (old.val : Set V2))
    (hxy : step.projection (step.inclusion (jfinal x)) =
      step.projection (step.inclusion (jfinal y))) :
    ∃ a b : Finset V3,
      a ∈ motion.freeComplex.faces ∧ a ∉ motion.fixedComplex.faces ∧
      b ∈ (motion.targets old).faces ∧
      Q (jfinal x) ∈ intrinsicInterior ℝ
        (convexHull ℝ (motion.coordinates.map 1 '' (a : Set V3))) ∧
      B (step.projection (step.inclusion (jfinal y))) ∈
        intrinsicInterior ℝ (convexHull ℝ (b : Set V3)) ∧
      a.card ≤ face.card ∧ b.card ≤ old.val.card ∧
      affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3) ∪ (b : Set V3)) =
        motion.plane ∧
      Module.finrank ℝ ((affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3)) ⊓
        affineSpan ℝ (b : Set V3)).direction) + Module.finrank ℝ motion.plane.direction =
        (a.card - 1) + (b.card - 1) := by
  have hxnext : x ∈ K₁.space := hsucc.symm.subset (Or.inr hx)
  have hxC : Q (j x) ∈ motion.support.space :=
    interior_subset (motion.active_supported x hxnext hxold)
  have hxK : x ∈ K.space := K.convexHull_subset_space hface hx
  let w := Q (jfinal x)
  have hwcoord : w = motion.coordinates.map 1 (Q (j x)) :=
    motion.coordinate_of_successor_agreement hnext hxnext hxQ hxC
  have hwC : w ∈ motion.support.space := by
    rw [hwcoord]
    exact (motion.coordinates.carrier 1).subset
      (mem_image_of_mem (motion.coordinates.map 1) hxC)
  have hfinalpoint : jfinal x = Q.symm (motion.coordinates.map 1 (Q (j x))) :=
    (hnext hxnext).trans (motion.chart_formula 1 hxQ)
  have hfinalQ : jfinal x ∈ Q.source := by
    rw [hfinalpoint]
    apply Q.map_target
    apply motion.support_upper
    rw [← hwcoord]
    exact hwC
  have hsource : w ∈ motion.coordinates.map 1 '' motion.source.space := by
    refine ⟨Q (j x), ?_, hwcoord.symm⟩
    rw [motion.source_space]
    exact ⟨⟨j x, ⟨mem_image_of_mem j hxnext, hxQ⟩, rfl⟩, hxC⟩
  have hfree : w ∉ motion.fixedSource.space := by
    intro hwfixed
    have hfixed : motion.coordinates.map 1 w = w :=
      motion.coordinates.fixed_protected 1 w hwfixed
    have hsame : Q (j x) = w := (motion.coordinates.map 1).injective
      (hwcoord.symm.trans hfixed.symm)
    rw [motion.protected_space] at hwfixed
    obtain ⟨⟨z, ⟨⟨xold, hxoldK, rfl⟩, hjoldQ⟩, hvalue⟩, _⟩ := hwfixed
    have hjx : j x = j xold := Q.injOn hxQ hjoldQ (hsame.trans hvalue.symm)
    have hxx : x = xold := hji hxK
      (SimplicialComplex.space_subset_of_le hK₀ hxoldK) hjx
    exact hxold (hxx.symm ▸ hxoldK)
  have hcommon : w = B (step.projection (step.inclusion (jfinal y))) := by
    change Q (jfinal x) = B (step.projection (step.inclusion (jfinal y)))
    rw [hval, hxy]
  have htarget : w ∈ (motion.targets old).space := by
    rw [motion.targets_space_of_prefix_agreement hold old]
    refine ⟨⟨step.projection (step.inclusion (jfinal y)), ?_, hcommon.symm⟩, hwC⟩
    refine ⟨mem_image_of_mem ((step.projection ∘ step.inclusion) ∘ jfinal) hy, ?_⟩
    have hyB := hmaps hfinalQ
    change step.projection (step.inclusion (jfinal x)) ∈ B.source at hyB
    rwa [hxy] at hyB
  obtain ⟨a, b, ha, ha0, hb, hwa, hwb, hspan, hbcard, hrank⟩ :=
    motion.exists_position_faces_at_intersection old hsource hfree htarget
  obtain ⟨L, _, _, _, hbound⟩ :=
    motion.exists_active_face_bound hK hface hsucc hj hQ
  refine ⟨a, b, ha, ha0, hb, hwa, ?_, (hbound a ha ha0).2, hbcard, hspan, hrank⟩
  rw [← hcommon]
  exact hwb

end Geometry.OriginalPLTower
