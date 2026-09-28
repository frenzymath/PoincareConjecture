import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Faces
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.FreeFaces
import PoincareConjecture.Proofs.M76.Dehn.OriginalIntersectionRankBounds











set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}







theorem FaceMotionData.exists_finite_intersection_cover
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} (hK : K.faces.Finite) (hK₀ : K₀ ≤ K)
    {face : Finset V2} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V2))
    {j : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (A : SimplicialComplex ℝ V2) (hA : A.space = Metric.sphere (0 : V2) 1)
    (old : K₀.faces)
    (hmarked : boundary = true → face ∈ A.faces ∧ old.val ∈ A.faces) :
    ∃ T : Finset (AffineSubspace ℝ V3),
      (∀ L ∈ T,
        (∃ a b : Finset V3, a ∈ motion.freeComplex.faces ∧
          b ∈ (motion.targets old).faces ∧
          L = affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3)) ⊓
            affineSpan ℝ (b : Set V3)) ∧
        Module.finrank ℝ L.direction ≤ 1 ∧
        (boundary = true → Module.finrank ℝ L.direction = 0) ∧
        ((face.card ≤ 2 ∨ old.val.card ≤ 2) → Module.finrank ℝ L.direction = 0)) ∧
      ∀ w ∈ motion.coordinates.map 1 '' motion.source.space,
        w ∉ motion.fixedSource.space → w ∈ (motion.targets old).space →
        ∃ L ∈ T, w ∈ L := by
  classical
  let candidates : Set (Finset V3 × Finset V3) :=
    motion.freeComplex.faces ×ˢ (motion.targets old).faces
  let overlap (p : Finset V3 × Finset V3) : AffineSubspace ℝ V3 :=
    affineSpan ℝ (motion.coordinates.map 1 '' (p.1 : Set V3)) ⊓
      affineSpan ℝ (p.2 : Set V3)
  let good : Set (Finset V3 × Finset V3) := candidates ∩
    {p | Module.finrank ℝ (overlap p).direction ≤ 1 ∧
      (boundary = true → Module.finrank ℝ (overlap p).direction = 0) ∧
      ((face.card ≤ 2 ∨ old.val.card ≤ 2) →
        Module.finrank ℝ (overlap p).direction = 0)}
  have hfinite : candidates.Finite :=
    (motion.subdivision_finite.subset motion.free_le).prod (motion.targets_finite old)
  have hgood : good.Finite := hfinite.subset inter_subset_left
  let T := (hgood.image overlap).toFinset
  refine ⟨T, ?_, ?_⟩
  · intro L hL
    obtain ⟨p, hp, rfl⟩ := (hgood.image overlap).mem_toFinset.mp hL
    exact ⟨⟨p.1, p.2, hp.1.1, hp.1.2, rfl⟩, hp.2⟩
  · intro w hsource hfree htarget
    obtain ⟨a, b, ha, ha0, hb, hwa, hwb, _, hbcard, hrank⟩ :=
      motion.exists_position_faces_at_intersection old hsource hfree htarget
    obtain ⟨_, _, _, _, hbound⟩ :=
      motion.exists_active_face_bound hK hface hsucc hj hQ
    have hranks := motion.original_intersection_rank_bounds A hA hface
      (hK₀ old.property) hmarked (hbound a ha ha0).2 hbcard hrank
    have hgoodab : (a, b) ∈ good :=
      ⟨⟨ha, hb⟩, hranks.2.2.1, hranks.2.2.2.1, hranks.2.2.2.2.1⟩
    refine ⟨overlap (a, b), (hgood.image overlap).mem_toFinset.mpr
      (mem_image_of_mem overlap hgoodab), ?_⟩
    exact ⟨convexHull_subset_affineSpan
      (s := motion.coordinates.map 1 '' (a : Set V3)) (intrinsicInterior_subset hwa),
      convexHull_subset_affineSpan (s := (b : Set V3)) (intrinsicInterior_subset hwb)⟩

end Geometry.OriginalPLTower
