import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalComplexEdgeGeometry

set_option autoImplicit false
open Set Geometry
namespace Geometry.SimplicialComplex
variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] [TopologicalSpace X]
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_edge_coordinates_with_cofaces
    (K : SimplicialComplex ℝ E) (g : E → X) (hg : InjOn g K.space)
    (e : ι → OpenPartialHomeomorph X V3)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo g (K.closedStar p).space B.source ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (K.closedStar p).AffineOnFaces (B ∘ g))
    (p q : E) (hpq : p ≠ q) (hpqK : ({p, q} : Finset E) ∈ K.faces) :
    ∃ B : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (segment ℝ p q) B.source ∧ B (g p) ≠ B (g q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        AffineMap.lineMap (B (g p)) (B (g q)) t ∈ B.target ∧
        B.symm (AffineMap.lineMap (B (g p)) (B (g q)) t) =
          g (AffineMap.lineMap p q t)) ∧
      B.symm '' segment ℝ (B (g p)) (B (g q)) = g '' segment ℝ p q ∧
      ∀ t ∈ K.faces, ({p, q} : Finset E) ⊆ t →
        MapsTo g (convexHull ℝ (t : Set E)) B.source ∧
        ∃ A : E →ᴬ[ℝ] V3, EqOn (B ∘ g) A (convexHull ℝ (t : Set E)) := by
  obtain ⟨B, hmap, hB, hface⟩ :=
    hstars p (K.face_subset_vertices hpqK (Finset.mem_insert_self _ _))
  have hstar : ({p, q} : Finset E) ∈ (K.closedStar p).faces := by
    refine ⟨hpqK, ?_⟩
    simpa only [Finset.insert_idem] using hpqK
  have hstarSeg : segment ℝ p q ⊆ (K.closedStar p).space := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      (K.closedStar p).convexHull_subset_space hstar
  have hseg : segment ℝ p q ⊆ K.space := by
    simpa only [Finset.coe_pair, convexHull_pair] using K.convexHull_subset_space hpqK
  have hsource : MapsTo g (segment ℝ p q) B.source := hmap.mono_left hstarSeg
  have hpB := hsource (left_mem_segment ℝ p q)
  have hqB := hsource (right_mem_segment ℝ p q)
  have hne : B (g p) ≠ B (g q) := by
    intro h
    exact hpq (hg (hseg (left_mem_segment ℝ p q)) (hseg (right_mem_segment ℝ p q))
      (B.injOn hpB hqB h))
  obtain ⟨A, hA⟩ := hface _ hstar
  have hAseg : EqOn (B ∘ g) A (segment ℝ p q) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hA
  have hcoord (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      B (g (AffineMap.lineMap p q t)) = AffineMap.lineMap (B (g p)) (B (g q)) t := by
    change (B ∘ g) (AffineMap.lineMap p q t) = _
    rw [hAseg (lineMap_mem_segment ℝ p q ht)]
    change A.toAffineMap (AffineMap.lineMap p q t) = _
    rw [A.toAffineMap.apply_lineMap]
    change AffineMap.lineMap (A p) (A q) t = _
    rw [← hAseg (left_mem_segment ℝ p q), ← hAseg (right_mem_segment ℝ p q)]
    rfl
  have hparameter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap (B (g p)) (B (g q)) t ∈ B.target ∧
      B.symm (AffineMap.lineMap (B (g p)) (B (g q)) t) =
        g (AffineMap.lineMap p q t) := by
    rw [← hcoord t ht]
    have hs := hsource (lineMap_mem_segment ℝ p q ht)
    exact ⟨B.map_source hs, B.left_inv hs⟩
  refine ⟨B, hB, hsource, hne, hparameter, ?_, ?_⟩
  · rw [segment_eq_image_lineMap, segment_eq_image_lineMap, image_image, image_image]
    exact image_congr (fun t ht => (hparameter t ht).2)
  · intro t ht hpt
    have hp : p ∈ t := hpt (Finset.mem_insert_self _ _)
    have htstar : t ∈ (K.closedStar p).faces :=
      ⟨ht, by simpa only [Finset.insert_eq_of_mem hp] using ht⟩
    exact ⟨hmap.mono_left ((K.closedStar p).convexHull_subset_space htstar), hface t htstar⟩

end Geometry.SimplicialComplex
