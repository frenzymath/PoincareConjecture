


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapEndpoints
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Widths








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
namespace OrientedEdgeGraphSubdivision

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)}
  (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
  (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
  (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s)))
  (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
  (hlocal : ∀ p q, q ∈ (P p).carrier →
    (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
  (cut : D.EdgeIndex → Bool → ℝ)
  (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) (1 / 3))
  (hmatch : ∀ a b, ∃ d : Bool × Bool,
    (P (D.edgeEndpoint a b)).radialSide d (B (D.edgeEndpoint a b)).scale =
      D.edgeFromEndpoint a b '' Icc 0 (cut a b))
  {e : D.EdgeIndex} {R : D.regions}
  {S : D.OrientedEdgeGraphSubdivision e R
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (cut e false) (1 - cut e true)}
  (L : D.CapGraphEndpoint P region chart B e R (S.piece S.firstPiece) false (cut e false))
  (T : D.CapGraphEndpoint P region chart B e R (S.piece S.lastPiece) true (cut e true))
  (K : S.CutChain L.direction T.direction)

include hdisjoint hlocal hcut hmatch



theorem CutChain.exists_cap_barriers (i : Fin S.count) :
    ∃ (ℓa ℓb : (ℝ × ℝ) →L[ℝ] ℝ) (Wa Wb : Set (ℝ × ℝ)),
      IsOpen Wa ∧ IsOpen Wb ∧
      ((S.piece i).parameter (S.cut i.castSucc),
        (S.piece i).lower ((S.piece i).parameter (S.cut i.castSucc))) ∈ Wa ∧
      ((S.piece i).parameter (S.cut i.succ),
        (S.piece i).lower ((S.piece i).parameter (S.cut i.succ))) ∈ Wb ∧
      ℓa ((S.piece i).frame (K.direction i.castSucc)) = 0 ∧
      ℓb ((S.piece i).frame (K.direction i.succ)) = 0 ∧
      0 < ℓa (1, deriv (S.piece i).lower ((S.piece i).parameter (S.cut i.castSucc))) ∧
      ℓb (1, deriv (S.piece i).lower ((S.piece i).parameter (S.cut i.succ))) < 0 ∧
      (∀ q ∈ D.graphCapObstacle region chart B R (S.piece i).frame ∩ Wa,
        ℓa (q - ((S.piece i).parameter (S.cut i.castSucc),
          (S.piece i).lower ((S.piece i).parameter (S.cut i.castSucc)))) ≤ 0) ∧
      ∀ q ∈ D.graphCapObstacle region chart B R (S.piece i).frame ∩ Wb,
        ℓb (q - ((S.piece i).parameter (S.cut i.succ),
          (S.piece i).lower ((S.piece i).parameter (S.cut i.succ)))) ≤ 0 := by
  have havoid := D.vertex_caps_disjoint_open_middleArc P B hdisjoint hlocal cut hcut hmatch e
  have hleft : ∃ (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (W : Set (ℝ × ℝ)),
      IsOpen W ∧
      ((S.piece i).parameter (S.cut i.castSucc),
        (S.piece i).lower ((S.piece i).parameter (S.cut i.castSucc))) ∈ W ∧
      ℓ ((S.piece i).frame (K.direction i.castSucc)) = 0 ∧
      0 < ℓ (1, deriv (S.piece i).lower ((S.piece i).parameter (S.cut i.castSucc))) ∧
      ∀ q ∈ D.graphCapObstacle region chart B R (S.piece i).frame ∩ W,
        ℓ (q - ((S.piece i).parameter (S.cut i.castSucc),
          (S.piece i).lower ((S.piece i).parameter (S.cut i.castSucc)))) ≤ 0 := by
    by_cases hi : i = S.firstPiece
    · subst i
      refine ⟨L.normal, L.neighborhood, L.neighborhood_open, ?_, ?_, ?_, ?_⟩
      · simpa only [S.firstPiece_castSucc, S.cut_first, Bool.false_eq_true, ite_false] using
          L.graph_mem_neighborhood
      · simpa only [S.firstPiece_castSucc, K.first] using L.normal_cut
      · simpa only [S.firstPiece_castSucc, S.cut_first, Bool.false_eq_true, ite_false] using
          L.normal_tangent
      · simpa only [S.firstPiece_castSucc, S.cut_first, Bool.false_eq_true, ite_false] using
          L.cap_separated
    · have hfirst : 0 < i.castSucc := by
        have hne : i.val ≠ 0 := fun hv => hi (Fin.ext hv)
        change 0 < i.val
        omega
      have htcut : S.cut i.castSucc ∈ Ioo (cut e false) (1 - cut e true) := by
        constructor
        · simpa only [S.cut_first] using S.cut_strictMono hfirst
        · simpa only [S.cut_last] using S.cut_strictMono (Fin.castSucc_lt_last i)
      obtain ⟨ℓ, W, hW, hmem, hker, hsign, hsep⟩ :=
        D.exists_internal_graph_cap_barrier region chart B R (S.piece i).frame e cut havoid
          (S.piece i).parameter (S.piece i).source_chart (S.piece i).graph_coordinates
          ((S.piece i).interval_source ⟨le_rfl, (S.cut_lt i).le⟩) htcut (K.left_transverse i) false
      exact ⟨ℓ, W, hW, hmem, hker, hsign, hsep⟩
  have hright : ∃ (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (W : Set (ℝ × ℝ)),
      IsOpen W ∧
      ((S.piece i).parameter (S.cut i.succ),
        (S.piece i).lower ((S.piece i).parameter (S.cut i.succ))) ∈ W ∧
      ℓ ((S.piece i).frame (K.direction i.succ)) = 0 ∧
      ℓ (1, deriv (S.piece i).lower ((S.piece i).parameter (S.cut i.succ))) < 0 ∧
      ∀ q ∈ D.graphCapObstacle region chart B R (S.piece i).frame ∩ W,
        ℓ (q - ((S.piece i).parameter (S.cut i.succ),
          (S.piece i).lower ((S.piece i).parameter (S.cut i.succ)))) ≤ 0 := by
    by_cases hi : i = S.lastPiece
    · subst i
      refine ⟨T.normal, T.neighborhood, T.neighborhood_open, ?_, ?_, ?_, ?_⟩
      · simpa only [S.lastPiece_succ, S.cut_last, ite_true] using T.graph_mem_neighborhood
      · simpa only [S.lastPiece_succ, K.last] using T.normal_cut
      · simpa only [S.lastPiece_succ, S.cut_last, ite_true] using T.normal_tangent
      · simpa only [S.lastPiece_succ, S.cut_last, ite_true] using T.cap_separated
    · have hlast : i.succ < Fin.last S.count := by
        have hne : i.succ ≠ Fin.last S.count := by
          intro he
          apply hi
          apply Fin.ext
          have hv := congrArg Fin.val he
          change i.val = S.count - 1
          change i.val + 1 = S.count at hv
          omega
        exact lt_of_le_of_ne (Fin.le_last i.succ) hne
      have htcut : S.cut i.succ ∈ Ioo (cut e false) (1 - cut e true) := by
        constructor
        · have hzero : 0 < i.succ := by change 0 < i.val + 1; omega
          simpa only [S.cut_first] using S.cut_strictMono hzero
        · simpa only [S.cut_last] using S.cut_strictMono hlast
      obtain ⟨ℓ, W, hW, hmem, hker, hsign, hsep⟩ :=
        D.exists_internal_graph_cap_barrier region chart B R (S.piece i).frame e cut havoid
          (S.piece i).parameter (S.piece i).source_chart (S.piece i).graph_coordinates
          ((S.piece i).interval_source ⟨(S.cut_lt i).le, le_rfl⟩) htcut (K.right_transverse i) true
      exact ⟨ℓ, W, hW, hmem, hker, hsign, hsep⟩
  obtain ⟨ℓa, Wa, hWa, ha, hka, hta, hsa⟩ := hleft
  obtain ⟨ℓb, Wb, hWb, hb, hkb, htb, hsb⟩ := hright
  exact ⟨ℓa, ℓb, Wa, Wb, hWa, hWb, ha, hb, hka, hkb, hta, htb, hsa, hsb⟩



theorem CutChain.exists_cap_avoiding_width (i : Fin S.count) :
    ∃ δ > 0, δ ≤ (K.graphCuts i).radius ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
        (t, z) ∈ ((K.graphCuts i).coordinates
          (S.piece i).parameter.open_target (S.piece i).lower_smooth).source) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
        (K.graphCuts i).coordinates (S.piece i).parameter.open_target (S.piece i).lower_smooth (t, z) ∉
          D.graphCapObstacle region chart B R (S.piece i).frame := by
  obtain ⟨ℓa, ℓb, Wa, Wb, hWa, hWb, ha, hb, hka, hkb, hta, htb, hsa, hsb⟩ :=
    K.exists_cap_barriers P region chart B hdisjoint hlocal cut hcut hmatch L T i
  obtain ⟨δ, hδ, hδP, hsource, havoid, _⟩ :=
    D.exists_graph_cap_avoiding_strip region chart B R (S.piece i).frame
      hdisjoint hlocal cut hcut hmatch e
      (S.cut_interval i.castSucc).1 (S.cut_interval i.succ).2
      (S.piece i).parameter (S.piece i).lower_smooth (S.piece i).interval_source
      (S.piece i).source_chart (S.piece i).parameter_image (S.piece i).graph_coordinates
      ((S.piece i).parameter_lt (S.cut_lt i)) (K.graphCuts i)
      ℓa ℓb hka hkb hta htb hWa hWb ha hb hsa hsb
  exact ⟨δ, hδ, hδP, hsource, havoid⟩

end OrientedEdgeGraphSubdivision
end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
