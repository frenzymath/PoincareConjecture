import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionRefinementJoins














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open PoincareConjecture.Topology.Surface.Euler

namespace PoincareConjecture




theorem m64Intrinsic_coordinate_parent_corner_retained
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    {S : I → Finset AnnulusCoordinates}
    (R : ∀ i, SmoothTriangleBoundarySubdivisionWithRefinement (F i) (b i) (S i))
    (i : I) (k : Fin 3) :
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
    exact refineByLines_exists_usedVertex M (R i).refinement_lines t k ht
  obtain ⟨u, w, hw, hpos⟩ := hused
  have hwRange : w ∈ Set.range ((R i).mesh.orderedVertex u) := by
    rw [(R i).mesh.range_orderedVertex]
    exact hw
  obtain ⟨j, hj⟩ := hwRange
  have hpos' : (R i).mesh.position ((R i).mesh.orderedVertex u j) = b i k := by
    rw [hj, hpos]
    rfl
  refine ⟨⟨F i ((R i).mesh.position ((R i).mesh.orderedVertex u j)), ?_⟩, ?_⟩
  · exact ⟨⟨⟨i, u⟩, j⟩, rfl⟩
  · exact congrArg (F i) hpos'

end PoincareConjecture
