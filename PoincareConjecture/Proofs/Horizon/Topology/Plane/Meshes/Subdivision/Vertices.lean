


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Subdivision.Fine








namespace Poincare.Topology.Plane.Meshes

open Set

private theorem mem_of_mem_convexHull_of_supporting_affine_zeros
    {s : Set Plane} {x : Plane} (f g : Plane →ᵃ[ℝ] ℝ)
    (hf : ∀ y ∈ s, 0 ≤ f y) (hg : ∀ y ∈ s, 0 ≤ g y)
    (hx : x ∈ convexHull ℝ s) (hfx : f x = 0) (hgx : g x = 0)
    (hunique : ∀ y, f y = 0 → g y = 0 → y = x) : x ∈ s := by
  have hxFirst : x ∈ convexHull ℝ (s ∩ {y | f y = 0}) := by
    rw [← convexHull_inter_affine_zero_of_nonneg_set s f hf]
    exact ⟨hx, hfx⟩
  have hxBoth : x ∈ convexHull ℝ ((s ∩ {y | f y = 0}) ∩ {y | g y = 0}) := by
    rw [← convexHull_inter_affine_zero_of_nonneg_set _ g (fun y hy => hg y hy.1)]
    exact ⟨hxFirst, hgx⟩
  obtain ⟨y, hy⟩ := convexHull_nonempty_iff.mp ⟨x, hxBoth⟩
  exact hunique y hy.1.2 hy.2 ▸ hy.1.1


noncomputable def vertexCuts (S : Finset Plane) : List (Plane →ᵃ[ℝ] ℝ) :=
  S.toList.flatMap fun x => [verticalCut (x 0), horizontalCut (x 1)]

theorem verticalCut_mem_vertexCuts {S : Finset Plane} {x : Plane} (hx : x ∈ S) :
    verticalCut (x 0) ∈ vertexCuts S := by
  simp only [vertexCuts, List.mem_flatMap]
  exact ⟨x, by simpa using hx, by simp⟩

theorem horizontalCut_mem_vertexCuts {S : Finset Plane} {x : Plane} (hx : x ∈ S) :
    horizontalCut (x 1) ∈ vertexCuts S := by
  simp only [vertexCuts, List.mem_flatMap]
  exact ⟨x, by simpa using hx, by simp⟩

namespace TriangleMesh

variable (M : TriangleMesh)



theorem mem_triangle_vertices_of_monochromatic
    {f g : Plane →ᵃ[ℝ] ℝ} (hf : M.IsMonochromatic f) (hg : M.IsMonochromatic g)
    {x : Plane} (hfx : f x = 0) (hgx : g x = 0)
    (hunique : ∀ y, f y = 0 → g y = 0 → y = x)
    {t : Finset M.Vertex} (ht : t ∈ M.triangles)
    (hx : x ∈ M.toPlaneComplex.cellCarrier t) : x ∈ M.position '' (t : Set M.Vertex) := by
  have orient (a : Plane →ᵃ[ℝ] ℝ) (ha : M.IsMonochromatic a) :
      ∃ b : Plane →ᵃ[ℝ] ℝ, (∀ v ∈ t, 0 ≤ b (M.position v)) ∧
        ∀ y, b y = 0 ↔ a y = 0 := by
    rcases ha t ht with ha | ha
    · exact ⟨a, ha, fun _ => Iff.rfl⟩
    · exact ⟨-a, (fun v hv => by simpa using ha v hv), fun y => by simp⟩
  obtain ⟨f', hf', hzeroF⟩ := orient f hf
  obtain ⟨g', hg', hzeroG⟩ := orient g hg
  apply mem_of_mem_convexHull_of_supporting_affine_zeros f' g'
    (fun y hy => ?_) (fun y hy => ?_) hx ((hzeroF x).mpr hfx) ((hzeroG x).mpr hgx)
    (fun y hyf hyg => hunique y ((hzeroF y).mp hyf) ((hzeroG y).mp hyg))
  · obtain ⟨v, hv, rfl⟩ := hy
    exact hf' v hv
  · obtain ⟨v, hv, rfl⟩ := hy
    exact hg' v hv


noncomputable def refineAtVertices (S : Finset Plane) : TriangleMesh :=
  M.refineByLines (vertexCuts S)

theorem refineAtVertices_subdivides (S : Finset Plane) :
    (M.refineAtVertices S).toPlaneComplex.Subdivides M.toPlaneComplex :=
  M.refineByLines_subdivides (vertexCuts S)

theorem refineAtVertices_support (S : Finset Plane) :
    (M.refineAtVertices S).toPlaneComplex.support = M.toPlaneComplex.support :=
  M.refineByLines_support (vertexCuts S)


theorem refineAtVertices_mem_triangle_vertices (S : Finset Plane)
    {x : Plane} (hxS : x ∈ S) {t : Finset (M.refineAtVertices S).Vertex}
    (ht : t ∈ (M.refineAtVertices S).triangles)
    (hx : x ∈ (M.refineAtVertices S).toPlaneComplex.cellCarrier t) :
    x ∈ (M.refineAtVertices S).position '' (t : Set (M.refineAtVertices S).Vertex) := by
  apply (M.refineAtVertices S).mem_triangle_vertices_of_monochromatic
    (M.refineByLines_isMonochromatic_of_mem (vertexCuts S) (verticalCut_mem_vertexCuts hxS))
    (M.refineByLines_isMonochromatic_of_mem (vertexCuts S) (horizontalCut_mem_vertexCuts hxS))
    (by simp) (by simp) ?_ ht hx
  intro y hy0 hy1
  apply plane_ext
  · simpa using sub_eq_zero.mp hy0
  · simpa using sub_eq_zero.mp hy1


theorem refineAtVertices_exists_incident_triangle (S : Finset Plane)
    {x : Plane} (hxS : x ∈ S) (hx : x ∈ M.toPlaneComplex.support) :
    ∃ t ∈ (M.refineAtVertices S).triangles,
      ∃ v ∈ t, (M.refineAtVertices S).position v = x := by
  have hx' : x ∈ (M.refineAtVertices S).toPlaneComplex.support := by
    rwa [M.refineAtVertices_support]
  rw [(M.refineAtVertices S).toPlaneComplex_support] at hx'
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx'
  obtain ⟨v, hv, hvx⟩ := M.refineAtVertices_mem_triangle_vertices S hxS ht hxt
  exact ⟨t, ht, v, hv, hvx⟩


theorem exists_subdivision_with_vertices (S : Finset Plane)
    (hS : (S : Set Plane) ⊆ M.toPlaneComplex.support) :
    ∃ N : TriangleMesh, N.toPlaneComplex.Subdivides M.toPlaneComplex ∧
      ∀ x ∈ S, ∃ t ∈ N.triangles, ∃ v ∈ t, N.position v = x := by
  refine ⟨M.refineAtVertices S, M.refineAtVertices_subdivides S, ?_⟩
  exact fun x hx => M.refineAtVertices_exists_incident_triangle S hx (hS hx)

end TriangleMesh

end Poincare.Topology.Plane.Meshes
