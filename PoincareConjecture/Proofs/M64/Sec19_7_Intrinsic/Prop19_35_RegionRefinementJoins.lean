import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionRefinement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OldVertices
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Cells














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open PoincareConjecture.Topology.Surface.Euler

namespace PoincareConjecture






theorem m64Intrinsic_exists_compatible_region_refinement_with_join_vertices
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hparents : ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (F i) (F j) (b i) (b j))
    (i0 i1 : I) (k0 k1 : Fin 3) :
    ∃ (S : I → Finset AnnulusCoordinates)
      (R : ∀ i, SmoothTriangleBoundarySubdivisionWithRefinement (F i) (b i) (S i)),
      ∃ (q0 q1 : Euler.CoordinateVertex
          (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
          (fun a => meshTriangleBasis (R a.1).mesh a.2)),
        q0.1 = F i0 (b i0 k0) ∧ q1.1 = F i1 (b i1 k1) := by
  obtain ⟨S, R, hcompat, hcover⟩ :=
    m64Intrinsic_exists_compatible_region_refinement F b hF hFi hsource hparents
  have hcorner (i : I) (k : Fin 3) :
      ∃ q : Euler.CoordinateVertex
          (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
          (fun a => meshTriangleBasis (R a.1).mesh a.2),
        q.1 = F i (b i k) := by
    let M := TriangleMesh.single (b i) (b i).ind
    let t : M.Triangle := ⟨Finset.univ, Finset.mem_singleton_self _⟩
    have ht : k ∈ t.1 := by simp [t]
    have hused : ∃ (u : (R i).mesh.Triangle) (w : (R i).mesh.Vertex),
        w ∈ u.1 ∧ (R i).mesh.position w = M.position k := by
      rw [(R i).mesh_eq_refineByLines]
      exact refineByLines_exists_usedVertex M (R i).refinement_lines t
        k ht
    obtain ⟨u, w, hw, hpos⟩ := hused
    have hw_range : w ∈ Set.range ((R i).mesh.orderedVertex u) := by
      rw [(R i).mesh.range_orderedVertex]
      exact hw
    obtain ⟨j, hj⟩ := hw_range
    have hpos' : (R i).mesh.position ((R i).mesh.orderedVertex u j) = (b i) k := by
      rw [hj, hpos]
      rfl
    refine ⟨⟨F i ((R i).mesh.position ((R i).mesh.orderedVertex u j)), ?_⟩, ?_⟩
    · refine ⟨⟨⟨i, u⟩, j⟩, rfl⟩
    · exact congrArg (F i) hpos'
  obtain ⟨q0, hq0⟩ := hcorner i0 k0
  obtain ⟨q1, hq1⟩ := hcorner i1 k1
  exact ⟨S, R, q0, q1, hq0, hq1⟩

end PoincareConjecture
