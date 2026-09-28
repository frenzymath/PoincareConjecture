import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.CutMembership

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface

theorem localMeshTriangles_vertex_old_or_cut (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {x : M.RefinedVertex f} (hx : x ∈ s) :
    (∃ v ∈ t.1, (x : Plane) = M.position v) ∨
      (x : Plane) ∈ localRefinementBoundaryCuts M f t := by
  unfold TriangleMesh.localMeshTriangles at hs
  unfold localRefinementBoundaryCuts
  split_ifs at hs ⊢ with hp hn hep hen
  · let o := Classical.choice hp
    rw [M.strictMeshFor_triangles] at hs
    obtain ⟨i, rfl⟩ := TriangleMesh.exists_index_of_mem_strictPattern _ hs hx
    fin_cases i
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right; exact List.mem_cons_self
    · right; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · let o := Classical.choice hn
    unfold TriangleMesh.strictNegativeMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [M.strictMeshFor_triangles] at hr
    obtain ⟨i, rfl⟩ := TriangleMesh.exists_index_of_mem_strictPattern _ hr hy
    fin_cases i
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      change affineCutPoint (-f) _ _ ∈ _
      rw [affineCutPoint.neg]
      exact List.mem_cons_self
    · right
      change affineCutPoint (-f) _ _ ∈ _
      rw [affineCutPoint.neg]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · let o := Classical.choice hep
    rw [M.edgeMeshFor_triangles] at hs
    obtain ⟨i, rfl⟩ := TriangleMesh.exists_index_of_mem_edgePattern _ hs hx
    fin_cases i
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right; exact List.mem_singleton_self _
  · let o := Classical.choice hen
    unfold TriangleMesh.edgeNegativeMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [M.edgeMeshFor_triangles] at hr
    obtain ⟨i, rfl⟩ := TriangleMesh.exists_index_of_mem_edgePattern _ hr hy
    fin_cases i
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · exact Or.inl ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      change affineCutPoint (-f) _ _ ∈ _
      rw [affineCutPoint.neg]
      exact List.mem_singleton_self _
  · unfold TriangleMesh.unchangedMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    have hr : r = Finset.univ := Finset.mem_singleton.mp hr
    subst r
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact Or.inl ⟨_, M.orderedVertex_mem t i, rfl⟩

theorem lineRefinementMesh_vertex_old_or_cut (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (u : (M.lineRefinementMesh f).Triangle)
    (x : (M.lineRefinementMesh f).Vertex) (hx : x ∈ u.1) :
    ∃ t : M.Triangle,
      (∃ v ∈ t.1, (M.lineRefinementMesh f).position x = M.position v) ∨
        (M.lineRefinementMesh f).position x ∈ localRefinementBoundaryCuts M f t := by
  obtain ⟨t, ht⟩ := M.mem_lineRefinementTriangles_iff f |>.mp u.2
  exact ⟨t, localMeshTriangles_vertex_old_or_cut M f t ht hx⟩

end PoincareConjecture.Topology.Surface
