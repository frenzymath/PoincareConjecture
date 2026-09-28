import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Ordering

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

def meshVertexAngleContribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (x : S) : ℝ :=
  ∑ t : M.Triangle, ∑ k : Fin 3, if F (meshTriangleBasis M t k) = x then
    coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0

section Reindex

variable (M : TriangleMesh) {V : Type} [Fintype V] [DecidableEq V]
  (p : V → EuclideanSpace ℝ (Fin 2)) (hp : Function.Injective p)
  (e : M.Vertex ↪ V) (he : ∀ v, p (e v) = M.position v)

def meshReindexTriangleEquiv : M.Triangle ≃ (M.reindex p hp e he).Triangle :=
  Equiv.ofBijective (fun t => ⟨t.1.map e, Finset.mem_image.mpr ⟨t.1, t.2, rfl⟩⟩) (by
    constructor
    · intro t u h
      apply Subtype.ext
      exact Finset.map_injective e (congrArg Subtype.val h)
    · rintro ⟨s, hs⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      exact ⟨⟨t, ht⟩, rfl⟩)

theorem range_meshTriangleBasis_reindex (t : M.Triangle) :
    range (meshTriangleBasis (M.reindex p hp e he) (meshReindexTriangleEquiv M p hp e he t)) =
      range (meshTriangleBasis M t) := by
  rw [range_meshTriangleBasis, range_meshTriangleBasis]
  change p '' (↑(t.1.map e) : Set V) = M.position '' (t.1 : Set M.Vertex)
  ext x
  simp only [mem_image, Finset.mem_coe, Finset.mem_map]
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, (he u).symm⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨e u, ⟨u, hu, rfl⟩, he u⟩

theorem meshVertexAngleContribution_reindex (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S) (x : S) :
    meshVertexAngleContribution g F (M.reindex p hp e he) x =
      meshVertexAngleContribution g F M x := by
  unfold meshVertexAngleContribution
  rw [← (meshReindexTriangleEquiv M p hp e he).sum_comp]
  apply Finset.sum_congr rfl
  intro t _
  exact coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _
    (range_meshTriangleBasis_reindex M p hp e he t) x

end Reindex

theorem meshVertexAngleContribution_single (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (p : Fin 3 → EuclideanSpace ℝ (Fin 2)) (hp : AffineIndependent ℝ p) (x : S) :
    meshVertexAngleContribution g F (TriangleMesh.single p hp) x =
      ∑ k : Fin 3, if F (p k) = x then
        coordinateTriangleAngle g F (affineBasisOfTriangle p hp) k else 0 := by
  let t : (TriangleMesh.single p hp).Triangle := ⟨Finset.univ, Finset.mem_singleton_self _⟩
  let : Unique (TriangleMesh.single p hp).Triangle := {
    default := t
    uniq := fun s => Subtype.ext (Finset.mem_singleton.mp s.2) }
  unfold meshVertexAngleContribution
  rw [Fintype.sum_unique]
  apply coordinateTriangle_vertex_contribution_eq_of_range_eq g F
    (meshTriangleBasis (TriangleMesh.single p hp) default) (affineBasisOfTriangle p hp) _ x
  rw [range_meshTriangleBasis]
  change p '' ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) = range p
  simp

theorem unchangedMeshFor_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (v : Fin 3 → M.Vertex) (hv : AffineIndependent ℝ (M.position ∘ v)) (x : S) :
    meshVertexAngleContribution g F (M.unchangedMeshFor f v hv) x =
      ∑ k : Fin 3, if F (M.position (v k)) = x then
        coordinateTriangleAngle g F (affineBasisOfTriangle (M.position ∘ v) hv) k else 0 := by
  rw [TriangleMesh.unchangedMeshFor, meshVertexAngleContribution_reindex]
  exact meshVertexAngleContribution_single g F _ hv x

theorem edgeNegativeMeshFor_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (v : Fin 3 → M.Vertex) (hv : AffineIndependent ℝ (M.position ∘ v))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range (M.position ∘ v)) ⊆ F.source)
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1))) (x : S) :
    let b := affineBasisOfTriangle (M.position ∘ v) hv
    meshVertexAngleContribution g F (M.edgeNegativeMeshFor f v hv h0 h1) x =
      (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) +
        if F (affineCutPoint f (M.position (v 0)) (M.position (v 1))) = x then Real.pi else 0 := by
  dsimp only
  rw [TriangleMesh.edgeNegativeMeshFor, meshVertexAngleContribution_reindex]
  simpa only [meshVertexAngleContribution, affineCutPoint.neg] using
    edgeMeshFor_vertex_contribution g F M (-f) v hv hF hFi hb (by simpa) (by simpa) x

theorem strictNegativeMeshFor_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (v : Fin 3 → M.Vertex) (hv : AffineIndependent ℝ (M.position ∘ v))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range (M.position ∘ v)) ⊆ F.source)
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : 0 < f (M.position (v 2))) (x : S) :
    let b := affineBasisOfTriangle (M.position ∘ v) hv
    meshVertexAngleContribution g F (M.strictNegativeMeshFor f v hv h0 h1 h2) x =
      (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) +
        (if F (affineCutPoint f (M.position (v 0)) (M.position (v 1))) = x then Real.pi else 0) +
        (if F (affineCutPoint f (M.position (v 0)) (M.position (v 2))) = x then Real.pi else 0) := by
  dsimp only
  rw [TriangleMesh.strictNegativeMeshFor, meshVertexAngleContribution_reindex]
  simpa only [meshVertexAngleContribution, affineCutPoint.neg] using
    strictMeshFor_vertex_contribution g F M (-f) v hv hF hFi hb
      (by simpa) (by simpa) (by simpa) x

end PoincareConjecture.Topology.Surface
