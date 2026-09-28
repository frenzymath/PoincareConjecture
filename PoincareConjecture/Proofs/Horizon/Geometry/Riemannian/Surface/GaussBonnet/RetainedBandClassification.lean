import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedOpenTopFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedLowerBoundaryFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandCutFans








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))



theorem canonical_vertex_fan_on_band_lowerArc_of_not_mem_caps
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ (T.bands p i).faces.lowerArc)
    (hcap : ∀ v s, q.1 ∉ ((T.caps v).face s).carrier) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  rw [(T.chains p).lowerArc_eq_original (T.bands p) i] at hq
  obtain ⟨t, ht, hq⟩ := hq
  have htrim := (T.graphs p).piece_interval_subset i ht
  have hleft : t ≠ T.cut p.1.2 false := by
    intro he
    obtain ⟨s, hs⟩ := T.cap_tip_mem_original_cap p.1.2 false
    apply hcap (T.decomposition.edgeEndpoint p.1.2 false) s
    have hpoint : T.decomposition.edgeFromEndpoint p.1.2 false (T.cut p.1.2 false) = q.1 := by
      simpa only [FiniteChartRegionDecomposition.edgeFromEndpoint, Bool.false_eq_true,
        ↓reduceIte, he] using hq
    exact hpoint ▸ hs
  have hright : t ≠ 1 - T.cut p.1.2 true := by
    intro he
    obtain ⟨s, hs⟩ := T.cap_tip_mem_original_cap p.1.2 true
    apply hcap (T.decomposition.edgeEndpoint p.1.2 true) s
    have hpoint : T.decomposition.edgeFromEndpoint p.1.2 true (T.cut p.1.2 true) = q.1 := by
      simpa only [FiniteChartRegionDecomposition.edgeFromEndpoint, ↓reduceIte, he] using hq
    exact hpoint ▸ hs
  exact T.canonical_vertex_fan_on_open_trimmed_edge_of_not_mem_caps g p.1.2 q
    ⟨lt_of_le_of_ne htrim.1 (Ne.symm hleft), lt_of_le_of_ne htrim.2 hright⟩ hq hcap



theorem canonical_vertex_fan_in_band_off_endpoint_cuts_of_not_mem_caps
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ (T.bands p i).faces.carrier)
    (hcap : ∀ v s, q.1 ∉ ((T.caps v).face s).carrier)
    (hleft : q.1 ∉ (T.bands p i).faces.leftCut)
    (hright : q.1 ∉ (T.bands p i).faces.rightCut) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  let B := T.bands p i
  by_cases hint : q.1 ∈ interior B.faces.carrier
  · exact T.canonical_vertex_fan_of_band_interior g p i q hint
  have hf : q.1 ∈ frontier B.faces.carrier := ⟨subset_closure hq, hint⟩
  rw [B.faces.frontier_carrier] at hf
  rcases hf with ((hlower | htop) | hl) | hr
  · exact T.canonical_vertex_fan_on_band_lowerArc_of_not_mem_caps g p i q hlower hcap
  · rw [← B.faces.height_graph_image] at htop
    obtain ⟨t, ht, he⟩ := htop
    have ht0 : t ≠ 0 := by
      intro h
      subst t
      apply hleft
      rw [← B.faces.left_height_image]
      exact ⟨B.faces.height 0, ⟨(B.faces.height_pos (by norm_num)).le, le_rfl⟩, he⟩
    have ht1 : t ≠ 1 := by
      intro h
      subst t
      apply hright
      rw [← B.faces.right_height_image]
      exact ⟨B.faces.height 1, ⟨(B.faces.height_pos (by norm_num)).le, le_rfl⟩, he⟩
    apply T.canonical_vertex_fan_on_interior_band_top g p i
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩ q
    exact he.symm.trans (B.coordinates_eq _)
  · exact False.elim (hleft hl)
  · exact False.elim (hright hr)



theorem exists_internal_band_cut_of_endpoint_cut_not_mem_caps
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    {q : S} (hcap : ∀ v s, q ∉ ((T.caps v).face s).carrier)
    (hq : q ∈ (T.bands p i).faces.leftCut ∪ (T.bands p i).faces.rightCut) :
    ∃ j k : Fin (T.graphs p).count, j.succ = k.castSucc ∧
      q ∈ (T.chains p).cutRay j.succ '' Icc (0 : ℝ) T.length := by
  rcases hq with hl | hr
  · have hne : i ≠ (T.graphs p).firstPiece := by
      intro he
      rw [he, T.first_band_leftCut_eq_chordSegment] at hl
      exact hcap _ _ ((T.leftCap p).chordSegment_subset_cap T.length_le_one hl)
    have hipos : 0 < i.val := by
      by_contra h
      exact hne (Fin.ext (by change i.val = 0; omega))
    let j : Fin (T.graphs p).count := ⟨i.val - 1, by omega⟩
    have hji : j.succ = i.castSucc := Fin.ext (by dsimp [j]; omega)
    refine ⟨j, i, hji, ?_⟩
    rw [hji, ← (T.chains p).leftCut_eq_cutRay (T.bands p) i]
    exact hl
  · have hne : i ≠ (T.graphs p).lastPiece := by
      intro he
      rw [he, T.last_band_rightCut_eq_chordSegment] at hr
      exact hcap _ _ ((T.rightCap p).chordSegment_subset_cap T.length_le_one hr)
    have hilt : i.val + 1 < (T.graphs p).count := by
      by_contra h
      exact hne (Fin.ext (by change i.val = (T.graphs p).count - 1; omega))
    let j : Fin (T.graphs p).count := ⟨i.val + 1, hilt⟩
    refine ⟨i, j, Fin.ext rfl, ?_⟩
    rw [← (T.chains p).rightCut_eq_cutRay (T.bands p) i]
    exact hr



theorem canonical_vertex_fan_on_half_open_band_cut_of_not_mem_caps
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i j : Fin (T.graphs p).count) (hij : i.succ = j.castSucc)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hcap : ∀ v s, q.1 ∉ ((T.caps v).face s).carrier)
    (hq : q.1 ∈ (T.chains p).cutRay i.succ '' Ico (0 : ℝ) T.length) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  obtain ⟨u, hu, he⟩ := hq
  by_cases hz : u = 0
  · subst u
    apply T.canonical_vertex_fan_on_band_lowerArc_of_not_mem_caps g p i q _ hcap
    rw [(T.chains p).lowerArc_eq_original (T.bands p) i]
    exact ⟨(T.graphs p).cut i.succ, ⟨((T.graphs p).cut_lt i).le, le_rfl⟩,
      ((T.chains p).right_cutRay_zero i).symm.trans he⟩
  · exact T.canonical_vertex_fan_on_open_band_cut g p i j hij q
      ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hz), hu.2⟩, he⟩

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
