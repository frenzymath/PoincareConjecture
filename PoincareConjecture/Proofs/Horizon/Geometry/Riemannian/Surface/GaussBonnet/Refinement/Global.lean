import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Local









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface




theorem localMeshTriangles_parent_unique (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t u : M.Triangle)
    {s : Finset (M.RefinedVertex f)}
    (ht : s ∈ M.localMeshTriangles f t) (hu : s ∈ M.localMeshTriangles f u) :
    t = u := by
  by_contra htu
  let a : (M.lineRefinementMesh f).Triangle :=
    ⟨s, M.mem_lineRefinementTriangles_iff f |>.mpr ⟨t, ht⟩⟩
  let b := meshTriangleBasis (M.lineRefinementMesh f) a
  have hsub : range b ⊆
      convexHull ℝ (range (meshTriangleBasis M t)) ∩
        convexHull ℝ (range (meshTriangleBasis M u)) := by
    simp only [range_meshTriangleBasis]
    intro z hz
    have hz' : z ∈ convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set _)) := by
      apply subset_convexHull
      simpa only [b, range_meshTriangleBasis, a, TriangleMesh.lineRefinementMesh] using hz
    exact ⟨M.convexHull_child_subset_parent f t ht hz',
      M.convexHull_child_subset_parent f u hu hz'⟩
  apply (affineIndependent_iff_not_collinear.mp b.ind)
  rcases meshTriangleBasis_pair_intersections M t u htu with
    ⟨k, l, hinter, _⟩ | ⟨v, _, hinter⟩
  · have hb (i : Fin 3) : b i ∈
        line[ℝ, meshTriangleBasis M t (k.succAbove 0),
          meshTriangleBasis M t (k.succAbove 1)] := by
      apply convexHull_subset_affineSpan
      rw [convexHull_pair, ← affineSegment_eq_segment, ← hinter]
      exact hsub (mem_range_self i)
    have heq : (b : Fin 3 → Plane) = ![b 0, b 1, b 2] := by
      funext i
      fin_cases i <;> rfl
    have hr := congrArg Set.range heq
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      insert_empty_eq] at hr
    rw [hr]
    exact collinear_triple_of_mem_affineSpan_pair (hb 0) (hb 1) (hb 2)
  · exact (collinear_singleton ℝ (M.position v)).subset (hsub.trans hinter)

private def MeshTriangleIdentification (N : TriangleMesh) {V : Type}
    (T : Finset (Finset V)) (p : V → Plane) :=
  {e : N.Triangle ≃ {s : Finset V // s ∈ T} //
    ∀ s, range (meshTriangleBasis N s) = p '' ((e s).1 : Set V)}

private def localMeshTriangleIdentification (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)
    (t : M.Triangle) :
    MeshTriangleIdentification (M.localRefinementMesh f t)
      (M.localMeshTriangles f t) ((↑) : M.RefinedVertex f → Plane) := by
  unfold TriangleMesh.localRefinementMesh TriangleMesh.localMeshTriangles
  split_ifs <;> exact ⟨Equiv.refl _, fun s => range_meshTriangleBasis _ s⟩


def localMeshTriangleEquiv (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)
    (t : M.Triangle) :
    (M.localRefinementMesh f t).Triangle ≃
      {s : Finset (M.RefinedVertex f) // s ∈ M.localMeshTriangles f t} :=
  (localMeshTriangleIdentification M f t).1

theorem range_meshTriangleBasis_localMeshTriangleEquiv (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle)
    (s : (M.localRefinementMesh f t).Triangle) :
    range (meshTriangleBasis (M.localRefinementMesh f t) s) =
      ((↑) : M.RefinedVertex f → Plane) ''
        ((localMeshTriangleEquiv M f t s).1 : Set (M.RefinedVertex f)) :=
  (localMeshTriangleIdentification M f t).2 s



def lineRefinementTriangleEquiv (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) :
    (Σ t : M.Triangle, (M.localRefinementMesh f t).Triangle) ≃
      (M.lineRefinementMesh f).Triangle :=
  Equiv.ofBijective (fun a =>
    ⟨(localMeshTriangleEquiv M f a.1 a.2).1,
      M.mem_lineRefinementTriangles_iff f |>.mpr
        ⟨a.1, (localMeshTriangleEquiv M f a.1 a.2).2⟩⟩) (by
    constructor
    · rintro ⟨t, s⟩ ⟨u, r⟩ h
      have hv : (localMeshTriangleEquiv M f t s).1 =
          (localMeshTriangleEquiv M f u r).1 := congrArg Subtype.val h
      have htu : t = u := localMeshTriangles_parent_unique M f t u
        (localMeshTriangleEquiv M f t s).2
        (hv ▸ (localMeshTriangleEquiv M f u r).2)
      subst u
      have hsr : s = r := (localMeshTriangleEquiv M f t).injective (Subtype.ext hv)
      subst r
      rfl
    · rintro ⟨s, hs⟩
      obtain ⟨t, ht⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
      refine ⟨⟨t, (localMeshTriangleEquiv M f t).symm ⟨s, ht⟩⟩, ?_⟩
      apply Subtype.ext
      change ((localMeshTriangleEquiv M f t)
        ((localMeshTriangleEquiv M f t).symm ⟨s, ht⟩)).1 = s
      simp only [Equiv.apply_symm_apply])

theorem range_meshTriangleBasis_lineRefinementTriangleEquiv (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle)
    (s : (M.localRefinementMesh f t).Triangle) :
    range (meshTriangleBasis (M.lineRefinementMesh f)
      (lineRefinementTriangleEquiv M f ⟨t, s⟩)) =
        range (meshTriangleBasis (M.localRefinementMesh f t) s) := by
  rw [range_meshTriangleBasis, range_meshTriangleBasis_localMeshTriangleEquiv]
  rfl

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem meshVertexAngleContribution_lineRefinementMesh
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) (x : S) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f) x =
      ∑ t : M.Triangle,
        meshVertexAngleContribution g F (M.localRefinementMesh f t) x := by
  unfold meshVertexAngleContribution
  rw [← (lineRefinementTriangleEquiv M f).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  exact coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _
    (range_meshTriangleBasis_lineRefinementTriangleEquiv M f t s) x





theorem lineRefinementMesh_vertex_contribution
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) (x : S) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f) x =
      meshVertexAngleContribution g F M x +
      ∑ t : M.Triangle, ∑ q ∈ (localRefinementBoundaryCuts M f t).toFinset,
        if F q = x then Real.pi else 0 := by
  rw [meshVertexAngleContribution_lineRefinementMesh]
  simp_rw [localRefinementMesh_vertex_contribution_finset g F M f _ hF hFi
    ((meshTriangleBasis_subset_support M _).trans hM) x]
  rw [Finset.sum_add_distrib]
  rfl

end PoincareConjecture.Topology.Surface
