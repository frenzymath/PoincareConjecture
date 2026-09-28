import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.TwoEdgeCut
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface

theorem exists_affineBasis_reindex_of_range_eq
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hrange : range b = range c) : ∃ e : Fin 3 ≃ Fin 3, b.reindex e = c := by
  have hmatch (i : Fin 3) : ∃ j, b j = c i := by
    have h : c i ∈ range b := by rw [hrange]; exact mem_range_self i
    exact h
  choose p hp using hmatch
  have hinj : Function.Injective p := by
    intro i j hij
    apply c.ind.injective
    exact (hp i).symm.trans ((congrArg b hij).trans (hp j))
  have hsurj : Function.Surjective p := by
    intro j
    have h : b j ∈ range c := by rw [← hrange]; exact mem_range_self j
    obtain ⟨i, hi⟩ := h
    exact ⟨i, b.ind.injective ((hp i).trans hi)⟩
  let e := Equiv.ofBijective p ⟨hinj, hsurj⟩
  refine ⟨e.symm, ?_⟩
  apply AffineBasis.ext
  funext i
  exact hp i

private theorem range_affineBasis_fin_three
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :
    range b = {b 0, b 1, b 2} := by
  rw [show (b : Fin 3 → EuclideanSpace ℝ (Fin 2)) = ![b 0, b 1, b 2] by
    funext i; fin_cases i <;> rfl]
  ext x
  simp only [Matrix.range_cons, Matrix.range_empty, mem_union, mem_singleton_iff,
    mem_empty_iff_false, mem_insert_iff, Matrix.cons_val]
  tauto

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem sum_coordinateTriangleAngle_eq_of_range_eq (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hrange : range b = range c) :
    (∑ k : Fin 3, coordinateTriangleAngle g F b k) =
      ∑ k : Fin 3, coordinateTriangleAngle g F c k := by
  obtain ⟨e, rfl⟩ := exists_affineBasis_reindex_of_range_eq b c hrange
  exact (sum_coordinateTriangleAngle_reindex g F b e).symm

theorem coordinateTriangle_vertex_contribution_eq_of_range_eq (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hrange : range b = range c) (x : S) :
    (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) =
      ∑ k : Fin 3, if F (c k) = x then coordinateTriangleAngle g F c k else 0 := by
  obtain ⟨e, rfl⟩ := exists_affineBasis_reindex_of_range_eq b c hrange
  exact (coordinateTriangle_vertex_contribution_reindex g F b e x).symm

def coordinateLineCutTriangle (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (i : Bool) : (M.edgeMeshFor f v hv h0 h1).Triangle :=
  ⟨{M.edgeVertices f v h0 h1 (if i then 1 else 0), M.edgeVertices f v h0 h1 2,
      M.edgeVertices f v h0 h1 3}, coordinateLineCutBasis_mem_edgeMeshFor M f v hv h0 h1 i⟩

theorem range_meshTriangleBasis_coordinateLineCutTriangle (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) (i : Bool) :
    range (meshTriangleBasis (M.edgeMeshFor f v hv h0 h1)
      (coordinateLineCutTriangle M f v hv h0 h1 i)) =
      range (coordinateLineCutBasis (affineBasisOfTriangle (M.position ∘ v) hv) f h0 h1 i) := by
  rw [range_meshTriangleBasis, range_affineBasis_fin_three]
  simp only [coordinateLineCutTriangle, Finset.coe_insert, Finset.coe_singleton,
    Set.image_insert_eq, Set.image_singleton, coordinateLineCutBasis_edgeVertices]
  rfl

def coordinateTwoEdgeCutTriangle (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i : Fin 3) :
    (M.strictMeshFor f v hv h0 h1 h2).Triangle :=
  ⟨{M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 0),
      M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 1),
      M.strictVertices f v h0 h1 h2 (coordinateTwoEdgeCutSlot i 2)},
    coordinateTwoEdgeCutBasis_mem_strictMeshFor M f v hv h0 h1 h2 i⟩

theorem range_meshTriangleBasis_coordinateTwoEdgeCutTriangle (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i : Fin 3) :
    range (meshTriangleBasis (M.strictMeshFor f v hv h0 h1 h2)
      (coordinateTwoEdgeCutTriangle M f v hv h0 h1 h2 i)) =
      range (coordinateTwoEdgeCutBasis (affineBasisOfTriangle (M.position ∘ v) hv) f h0 h1 h2 i) := by
  rw [range_meshTriangleBasis, range_affineBasis_fin_three]
  simp only [coordinateTwoEdgeCutTriangle, Finset.coe_insert, Finset.coe_singleton,
    Set.image_insert_eq, Set.image_singleton, coordinateTwoEdgeCutBasis_strictVertices]
  rfl

theorem coordinateLineCutTriangle_bijective (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    Function.Bijective (coordinateLineCutTriangle M f v hv h0 h1) := by
  constructor
  · intro i j hij
    have hinj : Function.Injective (fun i : Bool =>
        ({if i then 1 else 0, 2, 3} : Finset (Fin 4))) := by decide
    apply hinj
    apply Finset.map_injective (M.edgeVerticesEmbedding f v hv h0 h1)
    have hval := congrArg Subtype.val hij
    simpa only [coordinateLineCutTriangle, Finset.map_insert, Finset.map_singleton,
      TriangleMesh.edgeVerticesEmbedding, Function.Embedding.coeFn_mk] using hval
  · rintro ⟨t, ht'⟩
    have ht := ht'
    rw [M.edgeMeshFor_triangles] at ht
    simp only [TriangleMesh.edgePatternTriangles, Finset.mem_insert,
      Finset.mem_singleton] at ht
    rcases ht with ht | ht
    · exact ⟨false, Subtype.ext ht.symm⟩
    · exact ⟨true, Subtype.ext ht.symm⟩

def coordinateLineCutTriangleEquiv (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    Bool ≃ (M.edgeMeshFor f v hv h0 h1).Triangle :=
  Equiv.ofBijective (coordinateLineCutTriangle M f v hv h0 h1)
    (coordinateLineCutTriangle_bijective M f v hv h0 h1)

theorem coordinateTwoEdgeCutTriangle_bijective (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    Function.Bijective (coordinateTwoEdgeCutTriangle M f v hv h0 h1 h2) := by
  constructor
  · intro i j hij
    exact coordinateTwoEdgeCutBasis_face_injective M f v hv h0 h1 h2
      (congrArg Subtype.val hij)
  · rintro ⟨t, ht'⟩
    have ht := ht'
    rw [coordinateTwoEdgeCutBasis_strictMeshFor_triangles] at ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
    exact ⟨i, Subtype.ext hi⟩

def coordinateTwoEdgeCutTriangleEquiv (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    Fin 3 ≃ (M.strictMeshFor f v hv h0 h1 h2).Triangle :=
  Equiv.ofBijective (coordinateTwoEdgeCutTriangle M f v hv h0 h1 h2)
    (coordinateTwoEdgeCutTriangle_bijective M f v hv h0 h1 h2)

theorem edgeMeshFor_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (v : Fin 3 → M.Vertex) (hv : AffineIndependent ℝ (M.position ∘ v))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range (M.position ∘ v)) ⊆ F.source)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) (x : S) :
    let N := M.edgeMeshFor f v hv h0 h1
    let b := affineBasisOfTriangle (M.position ∘ v) hv
    (∑ t : N.Triangle, ∑ k : Fin 3, if F (meshTriangleBasis N t k) = x then
      coordinateTriangleAngle g F (meshTriangleBasis N t) k else 0) =
      (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) +
        if F (affineCutPoint f (M.position (v 0)) (M.position (v 1))) = x then Real.pi else 0 := by
  dsimp only
  let N := M.edgeMeshFor f v hv h0 h1
  let b := affineBasisOfTriangle (M.position ∘ v) hv
  let A (c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :=
    ∑ k : Fin 3, if F (c k) = x then coordinateTriangleAngle g F c k else 0
  change (∑ t : N.Triangle, A (meshTriangleBasis N t)) = _
  rw [← (coordinateLineCutTriangleEquiv M f v hv h0 h1).sum_comp
    (fun t => A (meshTriangleBasis N t))]
  have h (i : Bool) : A (meshTriangleBasis N
      (coordinateLineCutTriangleEquiv M f v hv h0 h1 i)) =
        A (coordinateLineCutBasis b f h0 h1 i) :=
    coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _
      (range_meshTriangleBasis_coordinateLineCutTriangle M f v hv h0 h1 i) x
  simp_rw [h]
  exact coordinateLineCutBasis_vertex_contribution g F b f hF hFi hb h0 h1 x

theorem strictMeshFor_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (v : Fin 3 → M.Vertex) (hv : AffineIndependent ℝ (M.position ∘ v))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range (M.position ∘ v)) ⊆ F.source)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (x : S) :
    let N := M.strictMeshFor f v hv h0 h1 h2
    let b := affineBasisOfTriangle (M.position ∘ v) hv
    (∑ t : N.Triangle, ∑ k : Fin 3, if F (meshTriangleBasis N t k) = x then
      coordinateTriangleAngle g F (meshTriangleBasis N t) k else 0) =
      (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) +
        (if F (affineCutPoint f (M.position (v 0)) (M.position (v 1))) = x then Real.pi else 0) +
        (if F (affineCutPoint f (M.position (v 0)) (M.position (v 2))) = x then Real.pi else 0) := by
  dsimp only
  let N := M.strictMeshFor f v hv h0 h1 h2
  let b := affineBasisOfTriangle (M.position ∘ v) hv
  let A (c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) :=
    ∑ k : Fin 3, if F (c k) = x then coordinateTriangleAngle g F c k else 0
  change (∑ t : N.Triangle, A (meshTriangleBasis N t)) = _
  rw [← (coordinateTwoEdgeCutTriangleEquiv M f v hv h0 h1 h2).sum_comp
    (fun t => A (meshTriangleBasis N t))]
  have h (i : Fin 3) : A (meshTriangleBasis N
      (coordinateTwoEdgeCutTriangleEquiv M f v hv h0 h1 h2 i)) =
        A (coordinateTwoEdgeCutBasis b f h0 h1 h2 i) :=
    coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _
      (range_meshTriangleBasis_coordinateTwoEdgeCutTriangle M f v hv h0 h1 h2 i) x
  simp_rw [h]
  exact coordinateTwoEdgeCutBasis_vertex_contribution g F b f hF hFi hb h0 h1 h2 x

end PoincareConjecture.Topology.Surface
