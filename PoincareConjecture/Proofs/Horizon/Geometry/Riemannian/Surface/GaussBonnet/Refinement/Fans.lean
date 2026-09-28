import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SubdivisionCorners
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Permutation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


theorem coordinateTriangle_vertex_contribution_reindex (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (e : Fin 3 ≃ Fin 3) (x : S) :
    (∑ k : Fin 3, if F (b.reindex e k) = x then
      coordinateTriangleAngle g F (b.reindex e) k else 0) =
      ∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0 := by
  simp only [coordinateTriangleAngle_reindex, AffineBasis.reindex_apply]
  exact e.symm.sum_comp (fun k => if F (b k) = x then coordinateTriangleAngle g F b k else 0)



theorem sum_coordinateSplitBasis_angles (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∑ i : Bool, ∑ k : Fin 3, coordinateTriangleAngle g F (coordinateSplitBasis b ht i) k) =
      (∑ k : Fin 3, coordinateTriangleAngle g F b k) + Real.pi := by
  obtain ⟨h0, hq⟩ := coordinateSplitBasis_angles g F b hF hFi hb ht
  obtain ⟨h1, h2⟩ := coordinateSplitBasis_endpoint_angles g F b hF hb ht
  simp only [Fintype.sum_bool, Fin.sum_univ_three]
  linarith only [h0, hq, h1, h2]



theorem coordinateSplitBasis_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : S) :
    (∑ i : Bool, ∑ k : Fin 3,
      if F (coordinateSplitBasis b ht i k) = x then
        coordinateTriangleAngle g F (coordinateSplitBasis b ht i) k else 0) =
      (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) +
        if F (AffineMap.lineMap (b 1) (b 2) t) = x then Real.pi else 0 := by
  classical
  obtain ⟨h0, hq⟩ := coordinateSplitBasis_angles g F b hF hFi hb ht
  obtain ⟨h1, h2⟩ := coordinateSplitBasis_endpoint_angles g F b hF hb ht
  simp only [Fintype.sum_bool, Fin.sum_univ_three, coordinateSplitBasis_apply,
    Bool.false_eq_true, if_false, if_true, Matrix.cons_val]
  split_ifs <;> linarith only [h0, hq, h1, h2]

omit [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S] in

theorem coordinateSplitBasis_cut_ne_vertex
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (k : Fin 3) :
    F (AffineMap.lineMap (b 1) (b 2) t) ≠ F (b k) := by
  intro heq
  have hv (i : Fin 3) := subset_convexHull ℝ (range b) (mem_range_self i)
  have hq := (convex_convexHull ℝ (range b)).lineMap_mem (hv 1) (hv 2)
    (Ioo_subset_Icc_self ht)
  have hcoord := congrArg (b.coord k) (F.injOn (hb hq) (hb (hv k)) heq)
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] at hcoord
  fin_cases k <;> norm_num [b.coord_apply, Fin.ext_iff] at hcoord <;> linarith [ht.1, ht.2]



theorem coordinateSplitBasis_new_vertex_fan (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∑ i : Bool, ∑ k : Fin 3,
      if F (coordinateSplitBasis b ht i k) = F (AffineMap.lineMap (b 1) (b 2) t) then
        coordinateTriangleAngle g F (coordinateSplitBasis b ht i) k else 0) = Real.pi := by
  have hne (k : Fin 3) := (coordinateSplitBasis_cut_ne_vertex F b hb ht k).symm
  simpa only [hne, if_false, Finset.sum_const_zero, if_true, zero_add] using
    coordinateSplitBasis_vertex_contribution g F b hF hFi hb ht
      (F (AffineMap.lineMap (b 1) (b 2) t))



theorem coordinateSplitBasis_old_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : S)
    (hx : F (AffineMap.lineMap (b 1) (b 2) t) ≠ x) :
    (∑ i : Bool, ∑ k : Fin 3,
      if F (coordinateSplitBasis b ht i k) = x then
        coordinateTriangleAngle g F (coordinateSplitBasis b ht i) k else 0) =
      ∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0 := by
  simpa only [hx, if_false, add_zero] using
    coordinateSplitBasis_vertex_contribution g F b hF hFi hb ht x



theorem coordinateSplitBasis_paired_cut_angle_sum (g : RiemannianMetric 2 S)
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hG : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G G.source)
    (hGi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G.symm G.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (hc : convexHull ℝ (range c) ⊆ G.source)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : F (AffineMap.lineMap (b 1) (b 2) t) = G (AffineMap.lineMap (c 1) (c 2) s)) :
    let x := F (AffineMap.lineMap (b 1) (b 2) t)
    (∑ i : Bool, ∑ k : Fin 3,
      if F (coordinateSplitBasis b ht i k) = x then
        coordinateTriangleAngle g F (coordinateSplitBasis b ht i) k else 0) +
    (∑ i : Bool, ∑ k : Fin 3,
      if G (coordinateSplitBasis c hs i k) = x then
        coordinateTriangleAngle g G (coordinateSplitBasis c hs i) k else 0) = 2 * Real.pi := by
  have hleft := coordinateSplitBasis_new_vertex_fan g F b hF hFi hb ht
  have hright := coordinateSplitBasis_new_vertex_fan g G c hG hGi hc hs
  rw [← hpoint] at hright
  dsimp only
  rw [hleft, hright]
  ring

end PoincareConjecture.Topology.Surface
