import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.Nonboundary
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.DualVertexFaceContainment
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall

set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (T : CoorientedSurfaceStars E)

local notation "C3" => ((ℝ × ℝ) × ℝ)

open Classical in

noncomputable def vertexBlock (p : (T.marked 2).vertices) : SimplicialComplex ℝ E :=
  let : Fintype T.ambient.faces := T.finite.fintype
  T.ambient.barycentricDualBlock {(p : E)}

theorem vertexBlock_subset_star (p : (T.marked 2).vertices) :
    (T.vertexBlock p).space ⊆ (T.ambient.closedStar p).space :=
  T.dualBlock_subset_star p (Finset.mem_singleton_self _)

theorem vertexBlock_chart (p : (T.marked 2).vertices) :
    (T.vertexBlock p).faces.Finite ∧ (p : E) ∈ (T.vertexBlock p).vertices ∧
      (T.vertexBlock p).closedStar p = T.vertexBlock p ∧
      (T.vertexBlock p).AffineOnFaces (T.chart p) ∧
      InjOn (T.chart p) (T.vertexBlock p).space ∧
      T.chart p p ∈ interior (T.chart p '' (T.vertexBlock p).space) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  let S := T.ambient.closedStar p
  have hpK : (p : E) ∈ T.ambient.vertices := T.marked_le 2 p.property
  have hN : N.faces.Finite := T.ambient.barycentricDualBlock_finite {p.val}
  have hpN : (p : E) ∈ N.vertices := by
    simpa only [N, vertexBlock, Finset.centroid_singleton, id_eq] using
      T.ambient.faceCentroid_mem_barycentricDualBlock_vertices hpK
  have hNstar : N.closedStar p = N := by
    simpa only [N, vertexBlock, Finset.centroid_singleton, id_eq] using
      T.ambient.barycentricDualBlock_closedStar_faceCentroid hpK
  have hNS := T.vertexBlock_subset_star p
  have hf : N.AffineOnFaces (T.chart p) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ :=
      T.ambient.exists_original_star_face_of_vertex_dual_face hpK hs
    obtain ⟨a, ha⟩ := T.star_affine p t ht
    exact ⟨a, fun _ hx => ha (hst hx)⟩
  have hi : InjOn (T.chart p) N.space := (T.star_injective p).mono hNS
  let K' := T.ambient.barycentricSubdivision
  have hK' : K'.faces.Finite := T.ambient.barycentricSubdivision_finite
  have hpK' : (p : E) ∈ K'.vertices :=
    (T.ambient.barycentricDualBlock_le {p.val}) hpN
  have hNs : N = K'.closedStar p :=
    T.ambient.barycentricDualBlock_singleton_eq_closedStar hpK
  obtain ⟨r, hr, hrN⟩ := K'.exists_ball_inter_space_subset_closedStar hK' hpK'
  have hnear : S.space ∩ ball (p : E) r ⊆ N.space := by
    intro x hx
    rw [hNs]
    apply hrN
    refine ⟨?_, hx.2⟩
    rw [T.ambient.barycentricSubdivision_isSubdivision.space_eq]
    exact T.star_subset_ambient p hx.1
  have hSc := S.isCompact_space_of_finite (finite_closedStar_faces T.finite p)
  have hfc : ContinuousOn (T.chart p) S.space :=
    (T.star_affine p).continuousOn (finite_closedStar_faces T.finite p)
  have hbad : IsClosed (T.chart p '' (S.space \ ball (p : E) r)) :=
    ((hSc.diff isOpen_ball).image_of_continuousOn (hfc.mono sdiff_subset)).isClosed
  have hpS : (p : E) ∈ S.space := hNS (N.vertices_subset_space hpN)
  have hpnot : T.chart p p ∉ T.chart p '' (S.space \ ball (p : E) r) := by
    rintro ⟨x, hx, hxp⟩
    have he := T.star_injective p hx.1 hpS hxp
    exact hx.2 (he ▸ mem_ball_self hr)
  have hsub : interior (T.chart p '' S.space) \
      T.chart p '' (S.space \ ball (p : E) r) ⊆ T.chart p '' N.space := by
    rintro y ⟨hy, hnot⟩
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    have hxb : x ∈ ball (p : E) r := by
      by_contra hn
      exact hnot ⟨x, ⟨hx, hn⟩, rfl⟩
    exact ⟨x, hnear ⟨hx, hxb⟩, rfl⟩
  exact ⟨hN, hpN, hNstar, hf, hi,
    interior_maximal hsub (isOpen_interior.inter hbad.isOpen_compl)
      ⟨T.star_interior p, hpnot⟩⟩

theorem vertex_base_eq_inter (p : (T.marked 2).vertices) :
    T.surfaceBase {(p : E)} = (T.vertexBlock p).space ∩ (T.marked 2).space := by
  change ((T.vertexBlock p).space ∩ (T.marked 0).space) ∩ (T.marked 2).space = _
  rw [inter_assoc, inter_eq_right.mpr T.surface_subset_region]

theorem vertex_base_rim_eq (p : (T.marked 2).vertices) :
    T.dualRegionRim {(p : E)} ∩ (T.marked 2).space =
      (T.surfaceBase {(p : E)} ∩ ((T.vertexBlock p).link p).space) ∪
        (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  have hlink : (N.link p).space ⊆ N.space :=
    space_subset_of_le (show N.link p ≤ N from fun _ hs => hs.1)
  have hrim : T.dualRegionRim {(p : E)} =
      ((N.link p).space ∩ (T.marked 0).space) ∪ (N.space ∩ (T.marked 1).space) := by
    dsimp only [dualRegionRim]
    rw [Finset.centroid_singleton]
    rfl
  rw [hrim, T.vertex_base_eq_inter]
  ext x
  constructor
  · rintro ⟨hx | hx, hxD⟩
    · exact Or.inl ⟨⟨hlink hx.1, hxD⟩, hx.1⟩
    · exact Or.inr ⟨⟨hx.1, hxD⟩, hx.2⟩
  · rintro (hx | hx)
    · exact ⟨Or.inl ⟨hx.2, T.surface_subset_region hx.1.2⟩, hx.1.2⟩
    · exact ⟨Or.inr ⟨hx.1.1, hx.2⟩, hx.1.2⟩

end Geometry.SimplicialComplex.CoorientedSurfaceStars
