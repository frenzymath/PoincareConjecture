import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.LineCut

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface

def coordinateTwoEdgeCutBasis
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (h2 : f (b 2) < 0) :
    Fin 3 → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  let l := coordinateLineCutBasis b f h0 h1 false
  let hl0 : 0 < f (l 0) := by simpa [l] using h0
  let hl1 : f (l 1) < 0 := by simpa [l] using h2
  ![coordinateLineCutBasis l f hl0 hl1 false,
    coordinateLineCutBasis b f h0 h1 true,
    coordinateLineCutBasis l f hl0 hl1 true]

@[simp] theorem coordinateTwoEdgeCutBasis_apply
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (h2 : f (b 2) < 0)
    (i k : Fin 3) :
    coordinateTwoEdgeCutBasis b f h0 h1 h2 i k =
      ![![b 0, affineCutPoint f (b 0) (b 1), affineCutPoint f (b 0) (b 2)],
        ![b 1, b 2, affineCutPoint f (b 0) (b 1)],
        ![b 2, affineCutPoint f (b 0) (b 1), affineCutPoint f (b 0) (b 2)]] i k := by
  fin_cases i <;> fin_cases k <;> simp [coordinateTwoEdgeCutBasis]

def coordinateTwoEdgeCutSlot (i k : Fin 3) : Fin 5 :=
  ![![0, 3, 4], ![1, 2, 3], ![2, 3, 4]] i k

theorem coordinateTwoEdgeCutSlot_face_injective :
    Function.Injective (fun i : Fin 3 =>
      ({coordinateTwoEdgeCutSlot i 0, coordinateTwoEdgeCutSlot i 1,
        coordinateTwoEdgeCutSlot i 2} : Finset (Fin 5))) := by
  decide

theorem coordinateTwoEdgeCutBasis_strictModelPosition
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (h2 : f (b 2) < 0)
    (i k : Fin 3) :
    coordinateTwoEdgeCutBasis b f h0 h1 h2 i k =
      TriangleMesh.strictModelPosition b f (coordinateTwoEdgeCutSlot i k) := by
  fin_cases i <;> fin_cases k <;>
    simp [coordinateTwoEdgeCutSlot, TriangleMesh.strictModelPosition]

theorem coordinateTwoEdgeCutBasis_affineReference
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (h2 : f (b 2) < 0)
    (i k : Fin 3) :
    coordinateTwoEdgeCutBasis b f h0 h1 h2 i k =
      triangleAffineEquiv standardTrianglePosition b standardTrianglePosition_affineIndependent b.ind
        (referenceSplitPosition (triangleCutParameter f (b 0) (b 1))
          (triangleCutParameter f (b 0) (b 2)) (coordinateTwoEdgeCutSlot i k)) := by
  rw [coordinateTwoEdgeCutBasis_strictModelPosition]
  exact TriangleMesh.strictModelPosition_eq_affineReference f b b.ind h0 h1 h2 _

theorem coordinateTwoEdgeCutBasis_hull_subset
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (h2 : f (b 2) < 0) (i : Fin 3) :
    convexHull ℝ (range (coordinateTwoEdgeCutBasis b f h0 h1 h2 i)) ⊆
      convexHull ℝ (range b) := by
  let l := coordinateLineCutBasis b f h0 h1 false
  have hl0 : 0 < f (l 0) := by simpa [l] using h0
  have hl1 : f (l 1) < 0 := by simpa [l] using h2
  fin_cases i
  · exact (coordinateLineCutBasis_hull_subset l f hl0 hl1 false).trans
      (coordinateLineCutBasis_hull_subset b f h0 h1 false)
  · exact coordinateLineCutBasis_hull_subset b f h0 h1 true
  · exact (coordinateLineCutBasis_hull_subset l f hl0 hl1 true).trans
      (coordinateLineCutBasis_hull_subset b f h0 h1 false)

theorem coordinateTwoEdgeCutBasis_hull_strictModelPosition
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (h2 : f (b 2) < 0) (i : Fin 3) :
    convexHull ℝ (range (coordinateTwoEdgeCutBasis b f h0 h1 h2 i)) =
      convexHull ℝ (TriangleMesh.strictModelPosition b f ''
        ({coordinateTwoEdgeCutSlot i 0, coordinateTwoEdgeCutSlot i 1,
          coordinateTwoEdgeCutSlot i 2} : Set (Fin 5))) := by
  congr 1
  ext x
  simp only [mem_range, mem_image, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨coordinateTwoEdgeCutSlot i k, ?_,
      (coordinateTwoEdgeCutBasis_strictModelPosition b f h0 h1 h2 i k).symm⟩
    fin_cases k <;> simp
  · rintro ⟨j, hj, rfl⟩
    rcases hj with rfl | rfl | rfl
    · exact ⟨0, coordinateTwoEdgeCutBasis_strictModelPosition b f h0 h1 h2 i 0⟩
    · exact ⟨1, coordinateTwoEdgeCutBasis_strictModelPosition b f h0 h1 h2 i 1⟩
    · exact ⟨2, coordinateTwoEdgeCutBasis_strictModelPosition b f h0 h1 h2 i 2⟩

theorem coordinateTwoEdgeCutBasis_strictVertices (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i k : Fin 3) :
    coordinateTwoEdgeCutBasis (affineBasisOfTriangle (M.position ∘ v) hv) f h0 h1 h2 i k =
      (M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i k) :
        EuclideanSpace ℝ (Fin 2)) := by
  rw [M.strictVertices_val]
  exact coordinateTwoEdgeCutBasis_strictModelPosition _ f h0 h1 h2 i k

theorem coordinateTwoEdgeCutBasis_mem_strictMeshFor (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i : Fin 3) :
    {M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 0),
      M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 1),
      M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 2)} ∈
        (M.strictMeshFor f v hv h0 h1 h2).triangles := by
  rw [M.strictMeshFor_triangles]
  fin_cases i <;> simp [coordinateTwoEdgeCutSlot, TriangleMesh.strictPatternTriangles]

theorem coordinateTwoEdgeCutBasis_strictMeshFor_triangles (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    (M.strictMeshFor f v hv h0 h1 h2).triangles = Finset.univ.image (fun i : Fin 3 =>
      {M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 0),
        M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 1),
        M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 2)}) := by
  rw [M.strictMeshFor_triangles, show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  simp [coordinateTwoEdgeCutSlot, TriangleMesh.strictPatternTriangles]

theorem coordinateTwoEdgeCutBasis_face_injective (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    Function.Injective (fun i : Fin 3 =>
      ({M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 0),
        M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 1),
        M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 2)} :
          Finset (M.RefinedVertex f))) := by
  intro i j hij
  apply coordinateTwoEdgeCutSlot_face_injective
  apply Finset.map_injective (M.strictVerticesEmbedding f v hv h0 h1 h2)
  simpa only [Finset.map_insert, Finset.map_singleton, TriangleMesh.strictVerticesEmbedding,
    Function.Embedding.coeFn_mk] using hij

theorem coordinateTwoEdgeCutBasis_cellCarrier (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i : Fin 3) :
    convexHull ℝ (range
      (coordinateTwoEdgeCutBasis (affineBasisOfTriangle (M.position ∘ v) hv) f h0 h1 h2 i)) =
      (M.strictMeshFor f v hv h0 h1 h2).toPlaneComplex.cellCarrier
        {M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 0),
          M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 1),
          M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 2)} := by
  rw [coordinateTwoEdgeCutBasis_hull_strictModelPosition,
    Poincare.Topology.Plane.Meshes.PlaneComplex.cellCarrier]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  fin_cases i <;> rfl

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem coordinateTwoEdgeCutBasis_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (h2 : f (b 2) < 0) (x : S) :
    (∑ i : Fin 3, ∑ k : Fin 3,
      if F (coordinateTwoEdgeCutBasis b f h0 h1 h2 i k) = x then
        coordinateTriangleAngle g F (coordinateTwoEdgeCutBasis b f h0 h1 h2 i) k else 0) =
      (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) +
        (if F (affineCutPoint f (b 0) (b 1)) = x then Real.pi else 0) +
        (if F (affineCutPoint f (b 0) (b 2)) = x then Real.pi else 0) := by
  let l := coordinateLineCutBasis b f h0 h1 false
  have hl0 : 0 < f (l 0) := by simpa [l] using h0
  have hl1 : f (l 1) < 0 := by simpa [l] using h2
  have hl : convexHull ℝ (range l) ⊆ F.source :=
    (coordinateLineCutBasis_hull_subset b f h0 h1 false).trans hb
  let A (c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :=
    ∑ k : Fin 3, if F (c k) = x then coordinateTriangleAngle g F c k else 0
  have hfirst := coordinateLineCutBasis_vertex_contribution g F b f hF hFi hb h0 h1 x
  have hsecond := coordinateLineCutBasis_vertex_contribution g F l f hF hFi hl hl0 hl1 x
  have hq : affineCutPoint f (l 0) (l 1) = affineCutPoint f (b 0) (b 2) := by
    simp [l]
  rw [hq] at hsecond
  change (∑ i : Bool, A (coordinateLineCutBasis b f h0 h1 i)) = _ at hfirst
  change (∑ i : Bool, A (coordinateLineCutBasis l f hl0 hl1 i)) = _ at hsecond
  simp only [Fintype.sum_bool] at hfirst hsecond
  change (∑ i : Fin 3, A (coordinateTwoEdgeCutBasis b f h0 h1 h2 i)) = _
  rw [Fin.sum_univ_three]
  change A (coordinateLineCutBasis l f hl0 hl1 false) +
    A (coordinateLineCutBasis b f h0 h1 true) +
    A (coordinateLineCutBasis l f hl0 hl1 true) = _
  change _ = A b + _ at hfirst
  change _ = A l + _ at hsecond
  linarith only [hfirst, hsecond]

theorem sum_coordinateTwoEdgeCutBasis_angles (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (h2 : f (b 2) < 0) :
    (∑ i : Fin 3, ∑ k : Fin 3,
      coordinateTriangleAngle g F (coordinateTwoEdgeCutBasis b f h0 h1 h2 i) k) =
      (∑ k : Fin 3, coordinateTriangleAngle g F b k) + 2 * Real.pi := by
  let l := coordinateLineCutBasis b f h0 h1 false
  have hl0 : 0 < f (l 0) := by simpa [l] using h0
  have hl1 : f (l 1) < 0 := by simpa [l] using h2
  have hl : convexHull ℝ (range l) ⊆ F.source :=
    (coordinateLineCutBasis_hull_subset b f h0 h1 false).trans hb
  let A (c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :=
    ∑ k : Fin 3, coordinateTriangleAngle g F c k
  have hfirst := sum_coordinateLineCutBasis_angles g F b f hF hFi hb h0 h1
  have hsecond := sum_coordinateLineCutBasis_angles g F l f hF hFi hl hl0 hl1
  change (∑ i : Bool, A (coordinateLineCutBasis b f h0 h1 i)) = A b + Real.pi at hfirst
  change (∑ i : Bool, A (coordinateLineCutBasis l f hl0 hl1 i)) = A l + Real.pi at hsecond
  simp only [Fintype.sum_bool] at hfirst hsecond
  change (∑ i : Fin 3, A (coordinateTwoEdgeCutBasis b f h0 h1 h2 i)) = A b + 2 * Real.pi
  rw [Fin.sum_univ_three]
  change A (coordinateLineCutBasis l f hl0 hl1 false) +
    A (coordinateLineCutBasis b f h0 h1 true) +
    A (coordinateLineCutBasis l f hl0 hl1 true) = _
  linarith only [hfirst, hsecond]

end PoincareConjecture.Topology.Surface
