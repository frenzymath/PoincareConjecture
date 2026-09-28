import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundaryHomeomorph
import PoincareConjecture.Proofs.M76.Smoothing.PlanarCircleComplex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false

open Set Geometry NormedSpace PoincareConjecture.M76.Smoothing

private noncomputable def reference_circle_homeomorph {n : ℕ} {theta : ℝ}
    (w : shortArcGapSpace n theta) : (planarCircleComplex w).space ≃ₜ Circle := by
  let K := planarCircleComplex w
  have hK : IsCompact K.space :=
    K.isCompact_space_of_finite (finite_planarCircleComplex_faces w)
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp hK
  have hc : ContinuousOn (NormedSpace.normalize : ℂ → ℂ) K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    apply (continuousAt_normalize_of_ne_zero ?_).continuousWithinAt
    intro hzero
    exact (linearIndependent_planarCircleComplex_face w hs).zero_notMem_convexHull
      (hzero ▸ hxs)
  let e : K.space ≃ₜ NormedSpace.normalize '' K.space :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn _ _ (injOn_normalize_planarCircleComplex w))
      (hc.domRestrict.subtype_mk _)
  exact e.trans (Homeomorph.setCongr (normalize_image_planarCircleComplex w))

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

theorem nonempty_boundary_homeomorph_circle (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P) :
    Nonempty (P.boundary ℝ ≃ₜ Circle) := by
  obtain ⟨w, hw⟩ := nonempty_shortArcGapSpace n
    (show Real.pi / 2 ∈ Ioo (0 : ℝ) Real.pi from
      ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩)
  let w' : shortArcGapSpace n (Real.pi / 2) := ⟨w, hw⟩
  let Q : Polygon ℂ (n + 3) := ⟨planarGapVertices w'⟩
  have hQ : Q.HasSimplicialEdges := by
    intro i j
    simpa only [Polygon.edgeSet, Polygon.edgeVertices, Finset.coe_pair,
      affineSegment_eq_segment, finRotate_apply, planarGapEdge] using
      planarGapEdge_inter_subset w' i j
  have hboundary : Q.boundary ℝ = (planarCircleComplex w').space := by
    simpa only [Polygon.boundary, Polygon.edgeSet, affineSegment_eq_segment,
      finRotate_apply, planarGapEdge] using (planarCircleComplex_space w').symm
  obtain ⟨e⟩ := P.nonempty_boundary_homeomorph Q hP hQ hinjP
    (injective_planarGapVertices w')
  exact ⟨(e.trans (Homeomorph.setCongr hboundary)).trans (reference_circle_homeomorph w')⟩

end Polygon
