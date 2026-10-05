import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Region.Refinement
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Refinement.InitialFans
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OriginalCorners
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Refinement.IndependentFans
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.VertexContributions

/-!
# Actual metric fans of the synchronized regional subdivisions

The stored finite line-refinement ancestry determines every used vertex
contribution. An interior point contributes two pi, a new boundary point
contributes pi, and an original corner retains its actual metric angle.
No angle-sum identity is supplied as a hypothesis.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle
open PoincareMT.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareMT

open Classical in
/-- The three possible metric contributions of a used vertex are derived from the actual
finite line-refinement construction. Source: Morgan--Tian Proposition 19.35, printed pp.
467-481, especially Claim 19.40, pp. 470-471; the explicit project tangent-fan derivation is
reviewed in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical
Checks. -/
theorem m64Intrinsic_subdivision_used_vertex_contribution
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates) (S : Finset AnnulusCoordinates)
    (R : SmoothTriangleBoundarySubdivisionWithRefinement F b S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) {q : AnnulusCoordinates}
    (hused : ∃ (t : R.mesh.Triangle) (v : R.mesh.Vertex),
      v ∈ t.1 ∧ F (R.mesh.position v) = q) :
    meshVertexAngleContribution g F R.mesh q =
      if q ∈ F '' interior (convexHull ℝ (range b)) then 2 * Real.pi else
        if q ∈ F '' range b then
          ∑ k : Fin 3, if F (b k) = q then coordinateTriangleAngle g F b k else 0
        else Real.pi := by
  classical
  rw [R.mesh_eq_refineByLines] at hused ⊢
  obtain ⟨t, v, hv, hvq⟩ := hused
  let M := (TriangleMesh.single b b.ind).refineByLines R.refinement_lines
  have hvsupport : M.position v ∈ M.toPlaneComplex.support := by
    rw [TriangleMesh.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨t.1, t.2, subset_convexHull ℝ _ ⟨v, hv, rfl⟩⟩
  have hvhull : M.position v ∈ convexHull ℝ (range b) := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support]
      using hvsupport
  have hvsource := hsource hvhull
  by_cases hinside : q ∈ F '' interior (convexHull ℝ (range b))
  · rw [if_pos hinside]
    obtain ⟨z, hz, hzq⟩ := hinside
    have hvz : M.position v = z := F.injOn hvsource
      (hsource (interior_subset hz)) (hvq.trans hzq.symm)
    have hvint : M.position v ∈ interior M.toPlaneComplex.support := by
      simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support, hvz] using hz
    rw [← hvq]
    exact single_refineByLines_interior_vertex_fan g F b R.refinement_lines
      hF hFi hsource t v hv hvint
  · rw [if_neg hinside]
    by_cases hcorner : q ∈ F '' range b
    · rw [if_pos hcorner]
      obtain ⟨z, ⟨k, rfl⟩, hkq⟩ := hcorner
      rw [← hkq, single_refineByLines_original_corner g F b R.refinement_lines
        hF hFi hsource k]
      have heq (j : Fin 3) : F (b j) = F (b k) ↔ j = k := by
        constructor
        · intro h
          exact b.ind.injective (F.injOn
            (hsource (subset_convexHull ℝ _ (mem_range_self j)))
            (hsource (subset_convexHull ℝ _ (mem_range_self k))) h)
        · rintro rfl
          rfl
      simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [if_neg hcorner, ← hvq]
      apply single_refineByLines_new_boundary_vertex_fan g F b R.refinement_lines
        hF hFi hsource t v hv
      · intro hint
        exact hinside ⟨M.position v, hint, hvq⟩
      · intro horiginal
        exact hcorner ⟨M.position v, horiginal, hvq⟩

/-- Used subdivision vertices inside a coordinate parent have their full two-pi metric fan,
independently of the surrounding parents. Source: Morgan--Tian Proposition 19.35, printed
pp. 467-481, especially Claim 19.40, pp. 470-471; the explicit project tangent-fan
derivation is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical Checks. -/
theorem m64Intrinsic_subdivision_interior_fan
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates) (S : Finset AnnulusCoordinates)
    (R : SmoothTriangleBoundarySubdivisionWithRefinement F b S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) {q : AnnulusCoordinates}
    (hused : ∃ (t : R.mesh.Triangle) (v : R.mesh.Vertex),
      v ∈ t.1 ∧ F (R.mesh.position v) = q)
    (hq : q ∈ F '' interior (convexHull ℝ (range b))) :
    meshVertexAngleContribution g F R.mesh q = 2 * Real.pi := by
  classical
  rw [m64Intrinsic_subdivision_used_vertex_contribution g F b S R hF hFi hsource hused,
    if_pos hq]

/-- A used point on an open original edge has the straight metric fan pi. Original corners
are excluded by affine-basis geometry. Source: Morgan--Tian Proposition 19.35, printed pp.
467-481, especially Claim 19.40, pp. 470-471; the explicit project tangent-fan derivation is
reviewed in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical
Checks. -/
theorem m64Intrinsic_subdivision_open_edge_fan
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates) (S : Finset AnnulusCoordinates)
    (R : SmoothTriangleBoundarySubdivisionWithRefinement F b S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) {q : AnnulusCoordinates}
    (hused : ∃ (t : R.mesh.Triangle) (v : R.mesh.Vertex),
      v ∈ t.1 ∧ F (R.mesh.position v) = q) (k : Fin 3)
    (hq : q ∈ F '' openSegment ℝ (b (k.succAbove 0)) (b (k.succAbove 1))) :
    meshVertexAngleContribution g F R.mesh q = Real.pi := by
  classical
  obtain ⟨z, hz, hzq⟩ := hq
  have hzfront := affineBasis_open_edge_subset_frontier b k hz
  have hzsource := hsource
    (((finite_range b).isCompact_convexHull ℝ).isClosed.frontier_subset hzfront)
  have hnotint : q ∉ F '' interior (convexHull ℝ (range b)) := by
    rintro ⟨w, hw, hwq⟩
    exact hzfront.2 ((F.injOn (hsource (interior_subset hw)) hzsource
      (hwq.trans hzq.symm)) ▸ hw)
  have hnotcorner : q ∉ F '' range b := by
    rintro ⟨w, ⟨j, rfl⟩, hjq⟩
    have heq := F.injOn (hsource (subset_convexHull ℝ _ (mem_range_self j))) hzsource
      (hjq.trans hzq.symm)
    exact affineBasis_vertex_not_mem_open_edge b k j (heq.symm ▸ hz)
  rw [m64Intrinsic_subdivision_used_vertex_contribution g F b S R hF hFi hsource hused,
    if_neg hnotint, if_neg hnotcorner]

end PoincareMT
