import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Refinement.MeshTransport
import PoincareLib.Topology.Surface.Euler.Cells

/-!
# Metric contributions at canonical geometric vertices

The vertex set is the range of the actual coordinate corners, as in the
geometric Euler bound. Regrouping by these points preserves every corner
slot, including corners shared by faces with different coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareMT.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

/-- The actual metric corner sum of a finite coordinate-face family at one
surface point. Coincident corners retain their face-slot multiplicity. -/
def coordinateVertexAngleContribution {I : Type*} [Fintype I]
    (g : RiemannianMetric 2 S) (F : I → OpenPartialHomeomorph Plane S)
    (b : I → AffineBasis (Fin 3) ℝ Plane) (x : S) : ℝ :=
  ∑ i, ∑ k : Fin 3, if F i (b i k) = x then coordinateTriangleAngle g (F i) (b i) k else 0

omit [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S] in
/-- Grouping actual corner slots by the canonical geometric vertex set is
an exact finite-sum identity, with no fan or incidence assumption. -/
theorem sum_coordinate_vertex_weights {I : Type*} [Fintype I]
    (F : I → OpenPartialHomeomorph Plane S) (b : I → AffineBasis (Fin 3) ℝ Plane)
    (w : I → Fin 3 → ℝ) :
    letI := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∑ v : Euler.CoordinateVertex F b, ∑ i, ∑ k : Fin 3,
      if F i (b i k) = v.1 then w i k else 0) = ∑ i, ∑ k : Fin 3, w i k := by
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have heq (v : Euler.CoordinateVertex F b) :
      F i (b i k) = v.1 ↔ Euler.coordinateCorner F b i k = v :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp only [heq, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The metric corner sum uses precisely the canonical vertices counted
by the geometric Euler theorem. -/
theorem sum_coordinateVertexAngleContribution {I : Type*} [Fintype I]
    (g : RiemannianMetric 2 S) (F : I → OpenPartialHomeomorph Plane S)
    (b : I → AffineBasis (Fin 3) ℝ Plane) :
    letI := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∑ v : Euler.CoordinateVertex F b, coordinateVertexAngleContribution g F b v.1) =
      ∑ i, ∑ k : Fin 3, coordinateTriangleAngle g (F i) (b i) k :=
  sum_coordinate_vertex_weights F b (fun i k => coordinateTriangleAngle g (F i) (b i) k)

/-- A single coordinate mesh has the existing pointwise contribution. -/
theorem coordinateVertexAngleContribution_mesh
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (x : S) :
    coordinateVertexAngleContribution g (fun _ : M.Triangle => F) (meshTriangleBasis M) x =
      meshVertexAngleContribution g F M x := rfl

/-- The actual child-face family of independently refined parent faces
has contribution equal to the sum of the individual mesh contributions. -/
theorem coordinateVertexAngleContribution_mesh_family {I : Type*} [Fintype I]
    (g : RiemannianMetric 2 S) (F : I → OpenPartialHomeomorph Plane S)
    (M : I → TriangleMesh) (x : S) :
    coordinateVertexAngleContribution g
      (fun t : (i : I) × (M i).Triangle => F t.1)
      (fun t : (i : I) × (M i).Triangle => meshTriangleBasis (M t.1) t.2) x =
        ∑ i, meshVertexAngleContribution g (F i) (M i) x := by
  unfold coordinateVertexAngleContribution meshVertexAngleContribution
  rw [Fintype.sum_sigma]

/-- Relabeling the actual face indices does not change their geometric
vertex contribution. -/
theorem coordinateVertexAngleContribution_reindex {I J : Type*} [Fintype I] [Fintype J]
    (g : RiemannianMetric 2 S) (F : I → OpenPartialHomeomorph Plane S)
    (b : I → AffineBasis (Fin 3) ℝ Plane) (e : J ≃ I) (x : S) :
    coordinateVertexAngleContribution g (F ∘ e) (b ∘ e) x =
      coordinateVertexAngleContribution g F b x := by
  unfold coordinateVertexAngleContribution
  exact Equiv.sum_comp e (fun i => ∑ k : Fin 3,
    if F i (b i k) = x then coordinateTriangleAngle g (F i) (b i) k else 0)

end PoincareMT.Topology.Surface
