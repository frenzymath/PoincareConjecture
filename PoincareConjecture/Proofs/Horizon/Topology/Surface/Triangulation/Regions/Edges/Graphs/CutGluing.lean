import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Intersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapGluing
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Gluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
namespace OrientedEdgeGraphSubdivision.CutChain

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  {S : D.OrientedEdgeGraphSubdivision e R C a b}
  {dLeft dRight : EuclideanSpace ℝ (Fin 2)} (K : S.CutChain dLeft dRight)
  {δ r : ℝ}
  (B : ∀ i : Fin S.count, (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)

def cutRay (k : Fin (S.count + 1)) (u : ℝ) : M :=
  C (C.symm ((D.edge e.1 e.2).map (S.cut k)) + u • K.direction k)

omit [T2Space M] in
theorem leftCut_eq_cutRay (i : Fin S.count) :
    (B i).faces.leftCut = K.cutRay i.castSucc '' Icc (0 : ℝ) r := by
  rw [(B i).leftCut_eq_ray (S.cut_lt i).le]
  simp only [cutRay, Prod.eta, ContinuousLinearEquiv.symm_apply_apply]

omit [T2Space M] in
theorem rightCut_eq_cutRay (i : Fin S.count) :
    (B i).faces.rightCut = K.cutRay i.succ '' Icc (0 : ℝ) r := by
  rw [(B i).rightCut_eq_ray (S.cut_lt i).le]
  simp only [cutRay, Prod.eta, ContinuousLinearEquiv.symm_apply_apply]

omit [T2Space M] in
theorem left_cutRay_zero (i : Fin S.count) :
    K.cutRay i.castSucc 0 = (D.edge e.1 e.2).map (S.cut i.castSucc) := by
  simp only [cutRay, zero_smul, add_zero]
  exact C.right_inv ((S.piece i).source_chart ((S.piece i).interval_source
    ⟨le_rfl, (S.cut_lt i).le⟩))

omit [T2Space M] in
theorem right_cutRay_zero (i : Fin S.count) :
    K.cutRay i.succ 0 = (D.edge e.1 e.2).map (S.cut i.succ) := by
  simp only [cutRay, zero_smul, add_zero]
  exact C.right_inv ((S.piece i).source_chart ((S.piece i).interval_source
    ⟨(S.cut_lt i).le, le_rfl⟩))

omit [T2Space M] in
theorem lowerArc_eq_original (i : Fin S.count) :
    (B i).faces.lowerArc = (D.edge e.1 e.2).map ''
      Icc (S.cut i.castSucc) (S.cut i.succ) := by
  simpa only [ObliqueBandFaces.lowerArc, linearGraphCoordinates_apply,
    collarParameterEquiv.apply_symm_apply] using (S.piece i).graph_image

omit [T2Space M] in
theorem adjacent_endpointEdge_image (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    ((B i).faces.endpointEdge true).map '' Icc (0 : ℝ) 1 =
      ((B j).faces.endpointEdge false).map '' Icc (0 : ℝ) 1 := by
  rw [(B i).faces.endpointEdge_image, (B j).faces.endpointEdge_image]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [K.rightCut_eq_cutRay B i, K.leftCut_eq_cutRay B j, hij]

omit [T2Space M] in
theorem adjacent_band_inter_subset_frontier (i j : Fin S.count) (hij : i.succ = j.castSucc)
    (hseparate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (S.piece i).strip (K.graphCuts i) (t, z) =
          (S.piece j).strip (K.graphCuts j) (s, w) → t = 1 ∧ s = 0) :
    (B i).faces.carrier ∩ (B j).faces.carrier ⊆ frontier (B i).faces.carrier := by
  have hright : (B i).faces.rightCut = C '' segment ℝ
      (C.symm ((D.edge e.1 e.2).map (S.cut i.succ)))
      (C.symm ((D.edge e.1 e.2).map (S.cut i.succ)) + r • K.direction i.succ) := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using
      (B i).rightCut_eq_segment (S.cut_lt i).le
  rw [K.adjacent_band_intersection B i j hij hseparate, ← hright]
  exact fun _ h => (B i).faces.outer_boundaries_subset_frontier (Or.inr h)

theorem open_cutRay_subset_interior_adjacent_union (i j : Fin S.count)
    (hij : i.succ = j.castSucc)
    (hseparate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (S.piece i).strip (K.graphCuts i) (t, z) =
          (S.piece j).strip (K.graphCuts j) (s, w) → t = 1 ∧ s = 0) :
    K.cutRay i.succ '' Ioo (0 : ℝ) r ⊆
      interior ((B i).faces.carrier ∪ (B j).faces.carrier) := by
  have hi : K.cutRay i.succ '' Ioo (0 : ℝ) r ⊆
      ((B i).faces.endpointEdge true).map '' Ioo (0 : ℝ) 1 := by
    simpa only [cutRay, Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using
      (B i).open_right_ray_subset_endpointEdge (S.cut_lt i).le
  have hj : K.cutRay i.succ '' Ioo (0 : ℝ) r ⊆
      ((B j).faces.endpointEdge false).map '' Ioo (0 : ℝ) 1 := by
    simpa only [cutRay, Prod.eta, ContinuousLinearEquiv.symm_apply_apply, hij] using
      (B j).open_left_ray_subset_endpointEdge (S.cut_lt j).le
  exact (subset_inter hi hj).trans
    ((B i).faces.shared_endpointCut_subset_interior_union (B j).faces true false
      (K.adjacent_endpointEdge_image B i j hij)
      (K.adjacent_band_inter_subset_frontier B i j hij hseparate))

private theorem frontier_iUnion_subset_of_internal_cut_cancellation
    (hcancel : ∀ i j : Fin S.count, i.succ = j.castSucc →
      K.cutRay i.succ '' Ioo (0 : ℝ) r ⊆ interior ((B i).faces.carrier ∪ (B j).faces.carrier))
    (htop : ∀ i : Fin S.count,
      K.cutRay i.castSucc r ∈ (B i).faces.polygonalTop ∧
      K.cutRay i.succ r ∈ (B i).faces.polygonalTop) :
    frontier (⋃ i, (B i).faces.carrier) ⊆
      (D.edge e.1 e.2).map '' Icc a b ∪ (⋃ i, (B i).faces.polygonalTop) ∪
        (B S.firstPiece).faces.leftCut ∪ (B S.lastPiece).faces.rightCut := by
  intro q hfront
  obtain ⟨i, hi⟩ := mem_iUnion.mp
    (Poincare.Topology.frontier_iUnion_subset_iUnion_frontier_of_isClosed
      (fun i => (B i).faces.carrier) (fun i => (B i).faces.isClosed_carrier) hfront)
  have hnot (j k : Fin S.count) : q ∉ interior ((B j).faces.carrier ∪ (B k).faces.carrier) := by
    intro hq
    exact hfront.2 (interior_mono (union_subset
      (subset_iUnion _ j) (subset_iUnion _ k)) hq)
  rw [(B i).faces.frontier_carrier] at hi
  rcases hi with ((hlower | hupper) | hleft) | hright
  · left; left; left
    rw [K.lowerArc_eq_original B i] at hlower
    exact image_mono (S.piece_interval_subset i) hlower
  · exact Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨i, hupper⟩)))
  · by_cases hfirst : i = S.firstPiece
    · exact Or.inl (Or.inr (hfirst ▸ hleft))
    rw [K.leftCut_eq_cutRay B i] at hleft
    obtain ⟨u, hu, rfl⟩ := hleft
    by_cases hu0 : u = 0
    · left; left; left
      rw [hu0, K.left_cutRay_zero i]
      exact ⟨S.cut i.castSucc, S.cut_interval i.castSucc, rfl⟩
    by_cases hur : u = r
    · left; left; right
      rw [hur]
      exact mem_iUnion.mpr ⟨i, (htop i).1⟩
    have hi0 : i.val ≠ 0 := fun h => hfirst (Fin.ext h)
    let j : Fin S.count := ⟨i.val - 1, by omega⟩
    have hji : j.succ = i.castSucc := by apply Fin.ext; dsimp [j]; omega
    exact False.elim (hnot j i (hcancel j i hji
      ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hur⟩, by rw [hji]⟩))
  · by_cases hlast : i = S.lastPiece
    · exact Or.inr (hlast ▸ hright)
    rw [K.rightCut_eq_cutRay B i] at hright
    obtain ⟨u, hu, rfl⟩ := hright
    by_cases hu0 : u = 0
    · left; left; left
      rw [hu0, K.right_cutRay_zero i]
      exact ⟨S.cut i.succ, S.cut_interval i.succ, rfl⟩
    by_cases hur : u = r
    · left; left; right
      rw [hur]
      exact mem_iUnion.mpr ⟨i, (htop i).2⟩
    have hilast : i.val ≠ S.count - 1 := fun h => hlast (Fin.ext h)
    let j : Fin S.count := ⟨i.val + 1, by have := i.isLt; omega⟩
    have hij : i.succ = j.castSucc := by apply Fin.ext; rfl
    exact False.elim (hnot i j (hcancel i j hij
      ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hur⟩, rfl⟩))

theorem frontier_iUnion_band_carrier_subset
    (hseparate : ∀ (i j : Fin S.count), i.succ = j.castSucc →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ z w : ℝ, |z| < δ → |w| < δ →
          (S.piece i).strip (K.graphCuts i) (t, z) =
            (S.piece j).strip (K.graphCuts j) (s, w) → t = 1 ∧ s = 0) :
    frontier (⋃ i, (B i).faces.carrier) ⊆
      (D.edge e.1 e.2).map '' Icc a b ∪ (⋃ i, (B i).faces.polygonalTop) ∪
        (B S.firstPiece).faces.leftCut ∪ (B S.lastPiece).faces.rightCut := by
  apply K.frontier_iUnion_subset_of_internal_cut_cancellation B
    (fun i j hij => K.open_cutRay_subset_interior_adjacent_union B i j hij (hseparate i j hij))
  intro i
  constructor
  · simpa only [cutRay, Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using
      (B i).left_top_mem_polygonalTop (S.cut_lt i).le
  · simpa only [cutRay, Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using
      (B i).right_top_mem_polygonalTop (S.cut_lt i).le

end OrientedEdgeGraphSubdivision.CutChain

private theorem image_Ioo_subset_of_image_Icc_eq {X : Type*} {f g : ℝ → X} {r : ℝ}
    (hf : InjOn f (Icc (0 : ℝ) 1))
    (hclosed : f '' Icc (0 : ℝ) 1 = g '' Icc (0 : ℝ) r)
    (hzero : f 0 = g 0) (hone : f 1 = g r) :
    f '' Ioo (0 : ℝ) 1 ⊆ g '' Ioo (0 : ℝ) r := by
  rintro q ⟨t, ht, rfl⟩
  have hm : f t ∈ g '' Icc (0 : ℝ) r := hclosed ▸
    mem_image_of_mem f (Ioo_subset_Icc_self ht)
  obtain ⟨u, hu, hgu⟩ := hm
  have hu0 : u ≠ 0 := by
    intro he
    rw [he] at hgu
    have h := hf (by simp) (Ioo_subset_Icc_self ht) (hzero.trans hgu)
    exact ht.1.ne h
  have hur : u ≠ r := by
    intro he
    rw [he] at hgu
    have h := hf (by simp) (Ioo_subset_Icc_self ht) (hone.trans hgu)
    exact ht.2.ne' h
  exact ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hur⟩, hgu⟩

namespace OrientedGraphPiece.FixedStripBandFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

omit [T2Space M] in

theorem left_open_endpointEdge_image (hab : a ≤ b) :
    (B.faces.endpointEdge false).map '' Ioo (0 : ℝ) 1 =
      (fun u : ℝ => C (C.symm ((D.edge e.1 e.2).map a) +
        u • G.frame.symm (ua, wa))) '' Ioo (0 : ℝ) ra := by
  apply subset_antisymm ?_ (B.open_left_ray_subset_endpointEdge hab)
  apply image_Ioo_subset_of_image_Icc_eq (B.faces.endpointEdge_injective false)
  · rw [B.faces.endpointEdge_image]
    exact B.leftCut_eq_ray hab
  · rw [B.faces.endpointEdge_map]
    change B.faces.coordinates (collarParameterEquiv.symm (0, 0 * B.faces.height 0)) = _
    rw [zero_mul, B.coordinates_eq]
    simpa only [P.left.parameter_zero] using G.strip_left_parameter P hab P.left.zero_mem_source
  · rw [B.faces.endpointEdge_map]
    change B.faces.coordinates (collarParameterEquiv.symm (0, 1 * B.faces.height 0)) = _
    rw [one_mul, B.coordinates_eq, B.height_zero]
    exact G.strip_left_parameter P hab B.left_parameter_mem

omit [T2Space M] in
theorem right_open_endpointEdge_image (hab : a ≤ b) :
    (B.faces.endpointEdge true).map '' Ioo (0 : ℝ) 1 =
      (fun u : ℝ => C (C.symm ((D.edge e.1 e.2).map b) +
        u • G.frame.symm (ub, wb))) '' Ioo (0 : ℝ) rb := by
  apply subset_antisymm ?_ (B.open_right_ray_subset_endpointEdge hab)
  apply image_Ioo_subset_of_image_Icc_eq (B.faces.endpointEdge_injective true)
  · rw [B.faces.endpointEdge_image]
    exact B.rightCut_eq_ray hab
  · rw [B.faces.endpointEdge_map]
    change B.faces.coordinates (collarParameterEquiv.symm (1, 0 * B.faces.height 1)) = _
    rw [zero_mul, B.coordinates_eq]
    simpa only [P.right.parameter_zero] using G.strip_right_parameter P hab P.right.zero_mem_source
  · rw [B.faces.endpointEdge_map]
    change B.faces.coordinates (collarParameterEquiv.symm (1, 1 * B.faces.height 1)) = _
    rw [one_mul, B.coordinates_eq, B.height_one]
    exact G.strip_right_parameter P hab B.right_parameter_mem

end OrientedGraphPiece.FixedStripBandFaces
end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
