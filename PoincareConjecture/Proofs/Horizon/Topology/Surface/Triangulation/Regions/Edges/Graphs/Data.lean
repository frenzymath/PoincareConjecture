


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.OrientedSubdivision
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.MiddleArcs








set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))


structure OrientedGraphPiece (e : D.EdgeIndex) (R : D.regions)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M) (a b : ℝ) where
  frame : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ)
  parameter : OpenPartialHomeomorph ℝ ℝ
  lower : ℝ → ℝ
  left : ℝ
  right : ℝ
  tubeLeft : ℝ
  tubeRight : ℝ
  tubeWidth : ℝ
  left_lt : left < a
  right_lt : b < right
  parameter_source : parameter.source = Ioo left right
  source_chart : parameter.source ⊆ (D.edge e.1 e.2).map ⁻¹' C.target
  parameter_strictMono : StrictMonoOn parameter parameter.source
  parameter_smooth : ContDiffOn ℝ ∞ parameter parameter.source
  parameter_symm_smooth : ContDiffOn ℝ ∞ parameter.symm parameter.target
  lower_smooth : ContDiffOn ℝ ∞ lower parameter.target
  graph_source : ∀ x ∈ parameter.target, frame.symm (x, lower x) ∈ C.source
  graph_coordinates : ∀ t ∈ parameter.source,
    frame (C.symm ((D.edge e.1 e.2).map t)) = (parameter t, lower (parameter t))
  graph_map : ∀ t ∈ parameter.source,
    (D.edge e.1 e.2).map t = C (frame.symm (parameter t, lower (parameter t)))
  positive_projection : ∀ t ∈ Icc a b,
    0 < (frame (deriv (C.symm ∘ (D.edge e.1 e.2).map) t)).1
  parameter_image : parameter '' Icc a b = Icc (parameter a) (parameter b)
  interval_target : Icc (parameter a) (parameter b) ⊆ parameter.target
  tube_left_lt : tubeLeft < parameter a
  tube_right_lt : parameter b < tubeRight
  tube_width_pos : 0 < tubeWidth
  tube : ∀ x ∈ Ioo tubeLeft tubeRight, ∀ z : ℝ, |z| < tubeWidth →
    frame.symm (x, lower x + z) ∈ C.source ∧
    (C (frame.symm (x, lower x + z)) ∈ chartDiskBoundaryUnion D.centers D.radius ↔ z = 0) ∧
    (C (frame.symm (x, lower x + z)) ∈ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ↔ 0 < z) ∧
    (0 ≤ z → C (frame.symm (x, lower x + z)) ∈ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R))


structure OrientedEdgeGraphSubdivision (e : D.EdgeIndex) (R : D.regions)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M) (a b : ℝ) where
  count : ℕ
  count_pos : 0 < count
  cut : Fin (count + 1) → ℝ
  cut_strictMono : StrictMono cut
  cut_first : cut 0 = a
  cut_last : cut (Fin.last count) = b
  cut_mem : ∀ i, cut i ∈ Ioo (0 : ℝ) 1
  piece : ∀ i : Fin count, D.OrientedGraphPiece e R C (cut i.castSucc) (cut i.succ)

namespace OrientedGraphPiece

variable {D} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  (P : D.OrientedGraphPiece e R C a b)

omit [T2Space M]

theorem interval_source : Icc a b ⊆ P.parameter.source := by
  rw [P.parameter_source]
  exact fun _ ht => ⟨P.left_lt.trans_le ht.1, ht.2.trans_lt P.right_lt⟩

theorem parameter_lt (hab : a < b) : P.parameter a < P.parameter b :=
  P.parameter_strictMono (P.interval_source ⟨le_rfl, hab.le⟩)
    (P.interval_source ⟨hab.le, le_rfl⟩) hab

theorem graph_image :
    (fun x => C (P.frame.symm (x, P.lower x))) ''
      Icc (P.parameter a) (P.parameter b) = (D.edge e.1 e.2).map '' Icc a b := by
  rw [← P.parameter_image, image_image]
  exact image_congr (fun t ht => (P.graph_map t (P.interval_source ht)).symm)

end OrientedGraphPiece

namespace OrientedEdgeGraphSubdivision

variable {D} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  (S : D.OrientedEdgeGraphSubdivision e R C a b)

omit [T2Space M]

theorem cut_lt (i : Fin S.count) : S.cut i.castSucc < S.cut i.succ :=
  S.cut_strictMono Fin.castSucc_lt_succ

theorem cut_interval (i : Fin (S.count + 1)) : S.cut i ∈ Icc a b := by
  constructor
  · simpa only [S.cut_first] using S.cut_strictMono.monotone (Fin.zero_le i)
  · simpa only [S.cut_last] using S.cut_strictMono.monotone (Fin.le_last i)

theorem piece_interval_subset (i : Fin S.count) :
    Icc (S.cut i.castSucc) (S.cut i.succ) ⊆ Icc a b :=
  Icc_subset_Icc (S.cut_interval i.castSucc).1 (S.cut_interval i.succ).2

theorem piece_interval_unit (i : Fin S.count) :
    Icc (S.cut i.castSucc) (S.cut i.succ) ⊆ Ioo (0 : ℝ) 1 :=
  fun _ ht => ⟨(S.cut_mem i.castSucc).1.trans_le ht.1,
    ht.2.trans_lt (S.cut_mem i.succ).2⟩

end OrientedEdgeGraphSubdivision


theorem exists_orientedEdgeGraphSubdivision (e : D.EdgeIndex) (R : D.regions)
    (hR : R = D.regionLeft e ∨ R = D.regionRight e)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    {a b : ℝ} (hab : a < b) (hparam : Icc a b ⊆ Ioo (0 : ℝ) 1)
    (hchart : (D.edge e.1 e.2).map '' Icc a b ⊆ C.target) :
    Nonempty (D.OrientedEdgeGraphSubdivision e R C a b) := by
  classical
  obtain ⟨n, c, hn, hc, hfirst, hlast, hcuts, hpieces⟩ :=
    D.exists_oriented_edge_graph_subdivision e R hR C hC hCinv hab hparam hchart
  refine ⟨⟨n, hn, c, hc, hfirst, hlast, hcuts, fun i => Classical.choice ?_⟩⟩
  obtain ⟨A, G, h, l, r, α, β, δ, hl, hr, hGs, hGC, hmono, hG, hGinv, hh,
    hsource, hcoordinates, hmap, hpositive, himage, htarget, hα, hβ, hδ, htube⟩ := hpieces i
  exact ⟨⟨A, G, h, l, r, α, β, δ, hl, hr, hGs, hGC, hmono, hG, hGinv, hh,
    hsource, hcoordinates, hmap, hpositive, himage, htarget, hα, hβ, hδ, htube⟩⟩


abbrev IncidentEdgeIndex :=
  {p : D.regions × D.EdgeIndex // p.1 = D.regionLeft p.2 ∨ p.1 = D.regionRight p.2}



theorem exists_incident_middleArc_graph_family
    (chart : D.regions → D.centers)
    (hchart : ∀ R : D.regions, closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R : M)).source)
    (cut : D.EdgeIndex → Bool → ℝ)
    (hcut : ∀ e t, cut e t ∈ Ioo (0 : ℝ) (1 / 3)) :
    Nonempty (∀ p : D.IncidentEdgeIndex,
      D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
        (cut p.1.2 false) (1 - cut p.1.2 true)) := by
  classical
  refine ⟨fun p => Classical.choice ?_⟩
  have hp := D.middleArc_parameters hcut p.1.2
  have hparam : Icc (cut p.1.2 false) (1 - cut p.1.2 true) ⊆ Ioo (0 : ℝ) 1 :=
    fun t ht => ⟨hp.1.trans_le ht.1, ht.2.trans_lt hp.2.2⟩
  apply D.exists_orientedEdgeGraphSubdivision p.1.2 p.1.1 p.2 _
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞)) hp.2.1 hparam
  rintro z ⟨t, ht, rfl⟩
  exact hchart p.1.1 (frontier_subset_closure
    ((D.edge_interior_incidence p.1.2 t (hparam ht) p.1.1).mpr p.2))

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
