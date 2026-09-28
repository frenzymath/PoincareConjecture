import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Fans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Permutation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface


def coordinateLineCutParentBasis
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  (b.reindex (Equiv.swap 0 2)).reindex (Equiv.swap 1 2)

@[simp] theorem coordinateLineCutParentBasis_apply
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (k : Fin 3) :
    coordinateLineCutParentBasis b k = ![b 2, b 0, b 1] k := by
  fin_cases k <;> simp [coordinateLineCutParentBasis, Equiv.swap_apply_def]

theorem coordinateLineCutParentBasis_hull
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    convexHull ℝ (range (coordinateLineCutParentBasis b)) =
      convexHull ℝ (range b) := by
  simp only [coordinateLineCutParentBasis, AffineBasis.coe_reindex, EquivLike.range_comp]

theorem coordinateLineCutParameter_mem
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) :
    triangleCutParameter f (b 0) (b 1) ∈ Ioo (0 : ℝ) 1 :=
  ⟨affineCutPoint.parameter_pos f _ _ h0 h1,
    affineCutPoint.parameter_lt_one f _ _ h0 h1⟩


def coordinateLineCutBasis
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (i : Bool) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  (coordinateSplitBasis (coordinateLineCutParentBasis b)
    (coordinateLineCutParameter_mem b f h0 h1) i).reindex
      (if i then (Equiv.swap 1 2).trans (Equiv.swap 0 1) else Equiv.swap 0 1)

@[simp] theorem coordinateLineCutBasis_apply
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (i : Bool) (k : Fin 3) :
    coordinateLineCutBasis b f h0 h1 i k =
      ![b (if i then 1 else 0), b 2, affineCutPoint f (b 0) (b 1)] k := by
  cases i <;> fin_cases k <;>
    simp [coordinateLineCutBasis, Equiv.swap_apply_def,
      affineCutPoint, triangleCutParameter]


theorem coordinateLineCutBasis_edgeModelPosition
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (i : Bool) (k : Fin 3) :
    coordinateLineCutBasis b f h0 h1 i k =
      TriangleMesh.edgeModelPosition b f (![if i then 1 else 0, 2, 3] k) := by
  cases i <;> fin_cases k <;>
    simp [TriangleMesh.edgeModelPosition]

theorem coordinateLineCutBasis_hull_subset
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (i : Bool) :
    convexHull ℝ (range (coordinateLineCutBasis b f h0 h1 i)) ⊆
      convexHull ℝ (range b) := by
  simp only [coordinateLineCutBasis, AffineBasis.coe_reindex, EquivLike.range_comp]
  rw [← coordinateLineCutParentBasis_hull b]
  exact coordinateSplitBasis_hull_subset _ _ i


theorem coordinateLineCutBasis_hull_edgeModelPosition
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (i : Bool) :
    convexHull ℝ (range (coordinateLineCutBasis b f h0 h1 i)) =
      convexHull ℝ (TriangleMesh.edgeModelPosition b f ''
        ({if i then 1 else 0, 2, 3} : Set (Fin 4))) := by
  congr 1
  ext x
  simp only [mem_range, mem_image, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨![if i then 1 else 0, 2, 3] k, ?_,
      (coordinateLineCutBasis_edgeModelPosition b f h0 h1 i k).symm⟩
    fin_cases k <;> simp
  · rintro ⟨j, hj, rfl⟩
    rcases hj with rfl | rfl | rfl
    · exact ⟨0, coordinateLineCutBasis_edgeModelPosition b f h0 h1 i 0⟩
    · exact ⟨1, coordinateLineCutBasis_edgeModelPosition b f h0 h1 i 1⟩
    · exact ⟨2, coordinateLineCutBasis_edgeModelPosition b f h0 h1 i 2⟩



theorem coordinateLineCutBasis_edgeVertices (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (i : Bool) (k : Fin 3) :
    coordinateLineCutBasis (affineBasisOfTriangle (M.position ∘ v) hv) f h0 h1 i k =
      (M.edgeVertices f v h0 h1 (![if i then 1 else 0, 2, 3] k) :
        EuclideanSpace ℝ (Fin 2)) := by
  rw [M.edgeVertices_val]
  exact coordinateLineCutBasis_edgeModelPosition _ f h0 h1 i k


theorem coordinateLineCutBasis_mem_edgeMeshFor (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (i : Bool) :
    {M.edgeVertices f v h0 h1 (if i then 1 else 0), M.edgeVertices f v h0 h1 2,
      M.edgeVertices f v h0 h1 3} ∈ (M.edgeMeshFor f v hv h0 h1).triangles := by
  classical
  rw [M.edgeMeshFor_triangles]
  cases i <;> simp [TriangleMesh.edgePatternTriangles]



theorem coordinateLineCutBasis_cellCarrier (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (i : Bool) :
    convexHull ℝ (range
      (coordinateLineCutBasis (affineBasisOfTriangle (M.position ∘ v) hv) f h0 h1 i)) =
      (M.edgeMeshFor f v hv h0 h1).toPlaneComplex.cellCarrier
        {M.edgeVertices f v h0 h1 (if i then 1 else 0), M.edgeVertices f v h0 h1 2,
          M.edgeVertices f v h0 h1 3} := by
  rw [coordinateLineCutBasis_hull_edgeModelPosition,
    Poincare.Topology.Plane.Meshes.PlaneComplex.cellCarrier]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  cases i <;> rfl

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem coordinateLineCutBasis_angle (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (i : Bool) (k : Fin 3) :
    coordinateTriangleAngle g F (coordinateLineCutBasis b f h0 h1 i) k =
      coordinateTriangleAngle g F
        (coordinateSplitBasis (coordinateLineCutParentBasis b)
          (coordinateLineCutParameter_mem b f h0 h1) i)
        ((if i then (Equiv.swap 1 2).trans (Equiv.swap 0 1)
          else Equiv.swap 0 1).symm k) :=
  coordinateTriangleAngle_reindex g F _ _ k



theorem sum_coordinateLineCutBasis_angles (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) :
    (∑ i : Bool, ∑ k : Fin 3,
      coordinateTriangleAngle g F (coordinateLineCutBasis b f h0 h1 i) k) =
      (∑ k : Fin 3, coordinateTriangleAngle g F b k) + Real.pi := by
  have hb' : convexHull ℝ (range (coordinateLineCutParentBasis b)) ⊆ F.source := by
    rwa [coordinateLineCutParentBasis_hull]
  simp only [coordinateLineCutBasis, sum_coordinateTriangleAngle_reindex]
  rw [sum_coordinateSplitBasis_angles g F _ hF hFi hb']
  simp only [coordinateLineCutParentBasis, sum_coordinateTriangleAngle_reindex]



theorem coordinateLineCutBasis_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) (x : S) :
    (∑ i : Bool, ∑ k : Fin 3,
      if F (coordinateLineCutBasis b f h0 h1 i k) = x then
        coordinateTriangleAngle g F (coordinateLineCutBasis b f h0 h1 i) k else 0) =
      (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) +
        if F (affineCutPoint f (b 0) (b 1)) = x then Real.pi else 0 := by
  classical
  have hb' : convexHull ℝ (range (coordinateLineCutParentBasis b)) ⊆ F.source := by
    rwa [coordinateLineCutParentBasis_hull]
  have hq : AffineMap.lineMap (coordinateLineCutParentBasis b 1)
      (coordinateLineCutParentBasis b 2) (triangleCutParameter f (b 0) (b 1)) =
        affineCutPoint f (b 0) (b 1) := by
    simp [affineCutPoint, triangleCutParameter]
  simp only [coordinateLineCutBasis, coordinateTriangle_vertex_contribution_reindex]
  rw [coordinateSplitBasis_vertex_contribution g F _ hF hFi hb', hq]
  simp only [coordinateLineCutParentBasis, coordinateTriangle_vertex_contribution_reindex]



theorem coordinateLineCutBasis_new_vertex_fan (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) :
    (∑ i : Bool, ∑ k : Fin 3,
      if F (coordinateLineCutBasis b f h0 h1 i k) =
          F (affineCutPoint f (b 0) (b 1)) then
        coordinateTriangleAngle g F (coordinateLineCutBasis b f h0 h1 i) k else 0) =
      Real.pi := by
  classical
  have hb' : convexHull ℝ (range (coordinateLineCutParentBasis b)) ⊆ F.source := by
    rwa [coordinateLineCutParentBasis_hull]
  simp only [coordinateLineCutBasis, coordinateTriangle_vertex_contribution_reindex]
  simpa only [coordinateLineCutParentBasis_apply, Matrix.cons_val,
    affineCutPoint, triangleCutParameter] using
    coordinateSplitBasis_new_vertex_fan g F (coordinateLineCutParentBasis b)
      hF hFi hb' (coordinateLineCutParameter_mem b f h0 h1)

end PoincareConjecture.Topology.Surface
