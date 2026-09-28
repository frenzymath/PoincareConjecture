import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Interfaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Widths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
private theorem linear_chart_cut_image
    (L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ)) (q v : ℝ × ℝ) (r : ℝ) :
    (fun z : ℝ × ℝ => linearGraphCoordinates C L (collarParameterEquiv.symm z)) ''
      segment ℝ q (q + r • v) = C '' segment ℝ (L.symm q) (L.symm q + r • L.symm v) := by
  have he : (fun z : ℝ × ℝ => linearGraphCoordinates C L (collarParameterEquiv.symm z)) =
      C ∘ L.symm := by
    funext z
    rw [linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply]
    rfl
  rw [he]
  change (fun z => C (L.symm z)) '' segment ℝ q (q + r • v) = _
  rw [← image_image (g := C) (f := L.symm)]
  apply congrArg (fun s => C '' s)
  change L.symm.toLinearMap.toAffineMap '' segment ℝ q (q + r • v) = _
  rw [image_segment]
  simp only [LinearMap.coe_toAffineMap, map_add, map_smul]
  rfl

omit [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
private theorem chart_segment_eq_ray (p d : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 ≤ r) :
    C '' segment ℝ p (p + r • d) = (fun t : ℝ => C (p + t • d)) '' Icc (0 : ℝ) r := by
  have hs : (fun t : ℝ => p + t • d) '' Icc (0 : ℝ) r = segment ℝ p (p + r • d) := by
    calc
      _ = (AffineMap.lineMap p (p + d)) '' segment ℝ (0 : ℝ) r := by
        rw [segment_eq_Icc hr]
        congr 1
        funext t
        simp [AffineMap.lineMap_apply, add_comm]
      _ = _ := by
        rw [image_segment]
        simp [AffineMap.lineMap_apply, add_comm]
  rw [← hs, image_image]

namespace OrientedGraphPiece.FixedStripBandFaces

variable {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

omit [T2Space M] in

theorem left_height_image (hab : a ≤ b) :
    (fun z => G.strip P (0, z)) '' Icc (0 : ℝ) (B.faces.height 0) =
      C '' segment ℝ (C.symm ((D.edge e.1 e.2).map a))
        (C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa)) := by
  have hmap : (fun z => G.strip P (0, z)) =
      fun z => B.faces.coordinates (collarParameterEquiv.symm (0, z)) :=
    funext (fun z => (B.coordinates_eq (0, z)).symm)
  have hbase : G.frame.symm (G.parameter a, G.lower (G.parameter a)) =
      C.symm ((D.edge e.1 e.2).map a) := by
    have h := congrArg G.frame.symm (G.graph_coordinates a
      (G.interval_source (left_mem_Icc.mpr hab)))
    simpa only [G.frame.symm_apply_apply] using h.symm
  rw [hmap, B.faces.left_height_image, ObliqueBandFaces.leftCut]
  have he : (G.parameter a + ra * ua, G.lower (G.parameter a) + ra * wa) =
      (G.parameter a, G.lower (G.parameter a)) + ra • (ua, wa) := by
    ext <;> simp [smul_eq_mul]
  rw [he, linear_chart_cut_image, hbase]

omit [T2Space M] in
theorem leftCut_eq_segment (hab : a ≤ b) :
    B.faces.leftCut = C '' segment ℝ (C.symm ((D.edge e.1 e.2).map a))
      (C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa)) := by
  rw [← B.left_height_image hab, ← B.faces.left_height_image]
  exact image_congr (fun z _ => B.coordinates_eq (0, z))

omit [T2Space M] in
theorem leftCut_eq_ray (hab : a ≤ b) :
    B.faces.leftCut = (fun t : ℝ =>
      C (C.symm ((D.edge e.1 e.2).map a) + t • G.frame.symm (ua, wa))) '' Icc (0 : ℝ) ra := by
  rw [B.leftCut_eq_segment hab, chart_segment_eq_ray _ _ B.faces.left_length_pos.le]

omit [T2Space M] in

theorem right_height_image (hab : a ≤ b) :
    (fun z => G.strip P (1, z)) '' Icc (0 : ℝ) (B.faces.height 1) =
      C '' segment ℝ (C.symm ((D.edge e.1 e.2).map b))
        (C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb)) := by
  have hmap : (fun z => G.strip P (1, z)) =
      fun z => B.faces.coordinates (collarParameterEquiv.symm (1, z)) :=
    funext (fun z => (B.coordinates_eq (1, z)).symm)
  have hbase : G.frame.symm (G.parameter b, G.lower (G.parameter b)) =
      C.symm ((D.edge e.1 e.2).map b) := by
    have h := congrArg G.frame.symm (G.graph_coordinates b
      (G.interval_source (right_mem_Icc.mpr hab)))
    simpa only [G.frame.symm_apply_apply] using h.symm
  rw [hmap, B.faces.right_height_image, ObliqueBandFaces.rightCut]
  have he : (G.parameter b + rb * ub, G.lower (G.parameter b) + rb * wb) =
      (G.parameter b, G.lower (G.parameter b)) + rb • (ub, wb) := by
    ext <;> simp [smul_eq_mul]
  rw [he, linear_chart_cut_image, hbase]

omit [T2Space M] in
theorem rightCut_eq_segment (hab : a ≤ b) :
    B.faces.rightCut = C '' segment ℝ (C.symm ((D.edge e.1 e.2).map b))
      (C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb)) := by
  rw [← B.right_height_image hab, ← B.faces.right_height_image]
  exact image_congr (fun z _ => B.coordinates_eq (1, z))

omit [T2Space M] in
theorem rightCut_eq_ray (hab : a ≤ b) :
    B.faces.rightCut = (fun t : ℝ =>
      C (C.symm ((D.edge e.1 e.2).map b) + t • G.frame.symm (ub, wb))) '' Icc (0 : ℝ) rb := by
  rw [B.rightCut_eq_segment hab, chart_segment_eq_ray _ _ B.faces.right_length_pos.le]

omit [T2Space M] in
theorem carrier_subset_open_strip :
    B.faces.carrier ⊆ G.strip P '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ) := by
  have hδ : 0 < δ := (B.height_bounds (by simp : (0 : ℝ) ∈ Icc 0 1)).1.trans
    (B.height_bounds (by simp : (0 : ℝ) ∈ Icc 0 1)).2
  refine B.carrier_subset_strip.trans (image_mono ?_)
  intro q hq
  exact ⟨hq.1, (neg_neg_of_pos hδ).trans_le hq.2.1, hq.2.2⟩

end OrientedGraphPiece.FixedStripBandFaces

omit [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] in
private theorem image_subgraph_slice (F : ℝ × ℝ → M) (h : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F '' ({q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
      {q | q.1 = t}) = (fun z => F (t, z)) '' Icc (0 : ℝ) (h t) := by
  ext p
  constructor
  · rintro ⟨⟨s, z⟩, ⟨⟨_, hz⟩, hst⟩, rfl⟩
    dsimp at hst hz
    subst s
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(t, z), ⟨⟨ht, hz⟩, rfl⟩, rfl⟩

namespace OrientedEdgeGraphSubdivision.CutChain

variable {S : D.OrientedEdgeGraphSubdivision e R C a b}
  {dLeft dRight : EuclideanSpace ℝ (Fin 2)} (K : S.CutChain dLeft dRight)
  {δ r : ℝ}
  (B : ∀ i : Fin S.count, (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)

omit [T2Space M] in

theorem adjacent_band_intersection (i j : Fin S.count) (hij : i.succ = j.castSucc)
    (hseparate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (S.piece i).strip (K.graphCuts i) (t, z) =
          (S.piece j).strip (K.graphCuts j) (s, w) → t = 1 ∧ s = 0) :
    (B i).faces.carrier ∩ (B j).faces.carrier =
      C '' segment ℝ (C.symm ((D.edge e.1 e.2).map (S.cut i.succ)))
        (C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ) := by
  rw [(B i).carrier_eq_fixed_strip, (B j).carrier_eq_fixed_strip]
  apply image_inter_eq_of_endpoint_separation
  · intro q hq v hv heq
    have hqheight : |q.2| < δ := by
      rw [abs_of_nonneg hq.2.1]
      exact hq.2.2.trans_lt ((B i).height_bounds hq.1).2
    have hvheight : |v.2| < δ := by
      rw [abs_of_nonneg hv.2.1]
      exact hv.2.2.trans_lt ((B j).height_bounds hv.1).2
    exact hseparate q.1 hq.1 v.1 hv.1 q.2 v.2 hqheight hvheight heq
  · rw [image_subgraph_slice _ _ (by simp), (B i).right_height_image (S.cut_lt i).le]
    simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply]
  · rw [image_subgraph_slice _ _ (by simp), (B j).left_height_image (S.cut_lt j).le]
    simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply, hij]

omit [T2Space M] in

theorem disjoint_band_carriers (i j : Fin S.count)
    (hseparate : Disjoint
      ((S.piece i).strip (K.graphCuts i) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ))
      ((S.piece j).strip (K.graphCuts j) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ))) :
    Disjoint (B i).faces.carrier (B j).faces.carrier :=
  hseparate.mono (B i).carrier_subset_open_strip (B j).carrier_subset_open_strip

end OrientedEdgeGraphSubdivision.CutChain
end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
