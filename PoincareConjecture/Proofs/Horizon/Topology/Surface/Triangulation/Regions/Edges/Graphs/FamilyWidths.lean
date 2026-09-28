


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Widths
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Arcs








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  (chart : D.regions → D.centers) (cut : D.EdgeIndex → Bool → ℝ)
  (S : ∀ p : D.IncidentEdgeIndex,
    D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
      (cut p.1.2 false) (1 - cut p.1.2 true))


abbrev IncidentGraphPieceIndex := Σ p : D.IncidentEdgeIndex, Fin (S p).count



def IncidentGraphPiecesSeparated (i j : D.IncidentGraphPieceIndex chart cut S) : Prop :=
  i.1.1.2 ≠ j.1.1.2 ∨ (i.1 = j.1 ∧
    (i.2.val + 1 < j.2.val ∨ j.2.val + 1 < i.2.val))

omit [T2Space M] in
theorem incidentGraphPiecesSeparated_disjoint
    (hcut : ∀ e t, cut e t ∈ Ioo (0 : ℝ) (1 / 3))
    (i j : D.IncidentGraphPieceIndex chart cut S)
    (hij : D.IncidentGraphPiecesSeparated chart cut S i j) :
    Disjoint ((S i.1).pieceArc i.2) ((S j.1).pieceArc j.2) := by
  rcases i with ⟨p, i⟩
  rcases j with ⟨q, j⟩
  rcases hij with hne | ⟨hpq, hgap⟩
  · exact D.incident_middleArc_pieceArcs_disjoint_of_edges_ne chart hcut S hne i j
  · dsimp at hpq
    subst q
    rcases hgap with hgap | hgap
    · exact (S p).disjoint_pieceArc_of_gap hgap
    · exact ((S p).disjoint_pieceArc_of_gap hgap).symm



theorem exists_incident_graph_strip_width
    (hcut : ∀ e t, cut e t ∈ Ioo (0 : ℝ) (1 / 3))
    (dLeft dRight : D.IncidentEdgeIndex → EuclideanSpace ℝ (Fin 2))
    (K : ∀ p, (S p).CutChain (dLeft p) (dRight p))
    (bound : ∀ p, Fin (S p).count → ℝ) (hbound : ∀ p i, 0 < bound p i) :
    ∃ δ > 0,
      (∀ p i, δ ≤ bound p i ∧ δ ≤ ((K p).graphCuts i).radius ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
          (t, z) ∈ (((S p).piece i).strip ((K p).graphCuts i)).source ∧
          (((S p).piece i).strip ((K p).graphCuts i) (t, z) ∈
            chartDiskBoundaryUnion D.centers D.radius ↔ z = 0) ∧
          (((S p).piece i).strip ((K p).graphCuts i) (t, z) ∈ connectedComponentIn
            (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1 ↔ 0 < z) ∧
          (0 ≤ z → ((S p).piece i).strip ((K p).graphCuts i) (t, z) ∈ closure (connectedComponentIn
            (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1))) ∧
      (∀ p (i j : Fin (S p).count), i.succ = j.castSucc →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ z w : ℝ, |z| < δ → |w| < δ →
            ((S p).piece i).strip ((K p).graphCuts i) (t, z) =
              ((S p).piece j).strip ((K p).graphCuts j) (s, w) → t = 1 ∧ s = 0) ∧
      ∀ i j : D.IncidentGraphPieceIndex chart cut S,
        D.IncidentGraphPiecesSeparated chart cut S i j →
          Disjoint
            (((S i.1).piece i.2).strip ((K i.1).graphCuts i.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ))
            (((S j.1).piece j.2).strip ((K j.1).graphCuts j.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ)) := by
  classical
  choose width hpos hregion hadjacent using
    fun p => (K p).exists_simultaneous_strip_width (bound p) (hbound p)
  let F := fun i : D.IncidentGraphPieceIndex chart cut S =>
    ((S i.1).piece i.2).strip ((K i.1).graphCuts i.2)
  have haxis (i : D.IncidentGraphPieceIndex chart cut S) :
      ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ (F i).source :=
    fun _ ht => ((S i.1).piece i.2).strip_axis_mem_source
      ((K i.1).graphCuts i.2) ((S i.1).cut_lt i.2) ht
  have hbase (i j : D.IncidentGraphPieceIndex chart cut S)
      (hij : D.IncidentGraphPiecesSeparated chart cut S i j) :
      Disjoint ((fun t => F i (t, 0)) '' Icc (0 : ℝ) 1)
        ((fun t => F j (t, 0)) '' Icc (0 : ℝ) 1) := by
    rw [show (fun t => F i (t, 0)) '' Icc (0 : ℝ) 1 = (S i.1).pieceArc i.2 from
      ((S i.1).piece i.2).strip_axis_image ((K i.1).graphCuts i.2) ((S i.1).cut_lt i.2)]
    rw [show (fun t => F j (t, 0)) '' Icc (0 : ℝ) 1 = (S j.1).pieceArc j.2 from
      ((S j.1).piece j.2).strip_axis_image ((K j.1).graphCuts j.2) ((S j.1).cut_lt j.2)]
    exact D.incidentGraphPiecesSeparated_disjoint chart cut S hcut i j hij
  obtain ⟨δ, hδ, hle, _, hseparate⟩ := exists_finite_disjoint_strip_width F haxis
    (D.IncidentGraphPiecesSeparated chart cut S) hbase
    (fun i => width i.1) (fun i => hpos i.1)
  have hδp (p : D.IncidentEdgeIndex) : δ ≤ width p := hle ⟨p, (S p).firstPiece⟩
  refine ⟨δ, hδ, ?_, ?_, hseparate⟩
  · intro p i
    refine ⟨(hδp p).trans (hregion p i).1, (hδp p).trans (hregion p i).2.1, ?_⟩
    exact fun t ht z hz => (hregion p i).2.2 t ht z (hz.trans_le (hδp p))
  · intro p i j hij t ht s hs z w hz hw heq
    exact hadjacent p i j hij t ht s hs z w
      (hz.trans_le (hδp p)) (hw.trans_le (hδp p)) heq

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
