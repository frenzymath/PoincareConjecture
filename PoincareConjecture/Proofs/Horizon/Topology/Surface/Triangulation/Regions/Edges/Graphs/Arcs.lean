


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Data
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Subdivision









set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

namespace OrientedEdgeGraphSubdivision

variable {D} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  (S : D.OrientedEdgeGraphSubdivision e R C a b)


def pieceArc (i : Fin S.count) : Set M :=
  (D.edge e.1 e.2).map '' Icc (S.cut i.castSucc) (S.cut i.succ)

omit [T2Space M]

theorem pieceArc_subset_arc (i : Fin S.count) :
    S.pieceArc i ⊆ (D.edge e.1 e.2).map '' Icc a b :=
  image_mono (S.piece_interval_subset i)

theorem pieceArc_subset_open_edge (i : Fin S.count) :
    S.pieceArc i ⊆ (D.edge e.1 e.2).map '' Ioo (0 : ℝ) 1 :=
  image_mono (S.piece_interval_unit i)

theorem pieceArc_left_mem (i : Fin S.count) :
    (D.edge e.1 e.2).map (S.cut i.castSucc) ∈ S.pieceArc i :=
  mem_image_of_mem _ ⟨le_rfl, (S.cut_lt i).le⟩

theorem pieceArc_right_mem (i : Fin S.count) :
    (D.edge e.1 e.2).map (S.cut i.succ) ∈ S.pieceArc i :=
  mem_image_of_mem _ ⟨(S.cut_lt i).le, le_rfl⟩

theorem isCompact_pieceArc (i : Fin S.count) : IsCompact (S.pieceArc i) :=
  isCompact_Icc.image_of_continuousOn ((D.edge e.1 e.2).smooth.continuousOn.mono
    ((S.piece_interval_unit i).trans Ioo_subset_Icc_self))


theorem pieceArc_eq_graph_image (i : Fin S.count) :
    S.pieceArc i =
      (fun x => C ((S.piece i).frame.symm (x, (S.piece i).lower x))) ''
        Icc ((S.piece i).parameter (S.cut i.castSucc))
          ((S.piece i).parameter (S.cut i.succ)) :=
  (S.piece i).graph_image.symm


theorem iUnion_pieceArc :
    (⋃ i, S.pieceArc i) = (D.edge e.1 e.2).map '' Icc a b := by
  simp only [pieceArc, ← image_iUnion]
  rw [iUnion_Icc_consecutive S.count_pos S.cut S.cut_strictMono.monotone,
    S.cut_first, S.cut_last]


theorem pieceArc_inter_of_adjacent {i j : Fin S.count}
    (hnext : (i : ℕ) + 1 = (j : ℕ)) :
    S.pieceArc i ∩ S.pieceArc j = {(D.edge e.1 e.2).map (S.cut i.succ)} := by
  have hindex : i.succ = j.castSucc := Fin.ext hnext
  apply Subset.antisymm
  · rintro q ⟨⟨t, ht, rfl⟩, u, hu, heq⟩
    have htu : u = t := D.edge_injective e.1 e.2
      (Ioo_subset_Icc_self (S.piece_interval_unit j hu))
      (Ioo_subset_Icc_self (S.piece_interval_unit i ht)) heq
    subst u
    have htcut : t = S.cut i.succ := le_antisymm ht.2 (by simpa [hindex] using hu.1)
    simp only [mem_singleton_iff, htcut]
  · intro q hq
    obtain rfl := mem_singleton_iff.mp hq
    exact ⟨S.pieceArc_right_mem i, by simpa only [hindex] using S.pieceArc_left_mem j⟩


theorem disjoint_pieceArc_of_gap {i j : Fin S.count}
    (hgap : (i : ℕ) + 1 < (j : ℕ)) :
    Disjoint (S.pieceArc i) (S.pieceArc j) := by
  have hlt : S.cut i.succ < S.cut j.castSucc := S.cut_strictMono hgap
  apply disjoint_left.mpr
  rintro q ⟨t, ht, rfl⟩ ⟨u, hu, heq⟩
  have htu : u = t := D.edge_injective e.1 e.2
    (Ioo_subset_Icc_self (S.piece_interval_unit j hu))
    (Ioo_subset_Icc_self (S.piece_interval_unit i ht)) heq
  subst u
  exact (not_lt_of_ge (hu.1.trans ht.2)) hlt


theorem disjoint_pieceArc_of_nonadjacent {i j : Fin S.count}
    (hne : i ≠ j) (hnext : (i : ℕ) + 1 ≠ (j : ℕ))
    (hprev : (j : ℕ) + 1 ≠ (i : ℕ)) :
    Disjoint (S.pieceArc i) (S.pieceArc j) := by
  have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact S.disjoint_pieceArc_of_gap (by omega)
  · exact (S.disjoint_pieceArc_of_gap (by omega : (j : ℕ) + 1 < (i : ℕ))).symm


theorem pieceArc_inter_subset_right {i j : Fin S.count} (hij : i < j) :
    S.pieceArc i ∩ S.pieceArc j ⊆ {(D.edge e.1 e.2).map (S.cut i.succ)} := by
  by_cases hnext : (i : ℕ) + 1 = (j : ℕ)
  · exact (S.pieceArc_inter_of_adjacent hnext).subset
  · have hgap : (i : ℕ) + 1 < (j : ℕ) := by
      have := Fin.lt_def.mp hij
      omega
    rw [(S.disjoint_pieceArc_of_gap hgap).inter_eq]
    exact empty_subset _

end OrientedEdgeGraphSubdivision

omit [T2Space M] in

theorem incident_middleArc_pieceArcs_cover
    (chart : D.regions → D.centers) (cut : D.EdgeIndex → Bool → ℝ)
    (S : ∀ p : D.IncidentEdgeIndex,
      D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
        (cut p.1.2 false) (1 - cut p.1.2 true))
    (p : D.IncidentEdgeIndex) :
    (⋃ i, (S p).pieceArc i) = D.middleArc cut p.1.2 :=
  (S p).iUnion_pieceArc

omit [T2Space M] in

theorem incident_middleArc_pieceArcs_disjoint_of_edges_ne
    (chart : D.regions → D.centers) {cut : D.EdgeIndex → Bool → ℝ}
    (hcut : ∀ e t, cut e t ∈ Ioo (0 : ℝ) (1 / 3))
    (S : ∀ p : D.IncidentEdgeIndex,
      D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
        (cut p.1.2 false) (1 - cut p.1.2 true))
    {p q : D.IncidentEdgeIndex} (hpq : p.1.2 ≠ q.1.2)
    (i : Fin (S p).count) (j : Fin (S q).count) :
    Disjoint ((S p).pieceArc i) ((S q).pieceArc j) :=
  (D.middleArc_disjoint_edge hcut hpq).mono ((S p).pieceArc_subset_arc i)
    (((S q).pieceArc_subset_open_edge j).trans (image_mono Ioo_subset_Icc_self))

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
