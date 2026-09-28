


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Data
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Cuts
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.CapTransversals








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))



structure CapGraphEndpoint
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
      (fun s => chart (region p s)))
    (e : D.EdgeIndex) (R : D.regions) {a b : ℝ}
    (g : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b)
    (terminal : Bool) (trim : ℝ) where
  sector : Bool × Bool
  radialEdge : Fin 3
  radialEdge_valid : radialEdge = 1 ∨ radialEdge = 2
  sector_region : region (D.edgeEndpoint e terminal) sector = R
  endpoint_parameter : (if terminal then b else a) = (if terminal then 1 - trim else trim)
  radial_image :
    (((B (D.edgeEndpoint e terminal)).face sector).boundary radialEdge).map '' Icc (0 : ℝ) 1 =
      D.edgeFromEndpoint e terminal '' Icc 0 trim
  radial_start : (((B (D.edgeEndpoint e terminal)).face sector).boundary radialEdge).map 0 =
    (D.edgeEndpoint e terminal : M)
  radial_end : (((B (D.edgeEndpoint e terminal)).face sector).boundary radialEdge).map 1 =
    D.edgeFromEndpoint e terminal trim
  direction : EuclideanSpace ℝ (Fin 2)
  direction_eq : direction = (B (D.edgeEndpoint e terminal)).chordDirection sector (decide (radialEdge = 1))
  direction_ne_zero : direction ≠ 0
  chord_base : (B (D.edgeEndpoint e terminal)).chordEndpoint sector (decide (radialEdge = 1)) =
    chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim)
  transverse : 0 < (g.frame direction).2 -
    deriv g.lower (g.parameter (if terminal then 1 - trim else trim)) * (g.frame direction).1
  normal : (ℝ × ℝ) →L[ℝ] ℝ
  normal_cut : normal (g.frame direction) = 0
  normal_tangent : if terminal then
      normal (1, deriv g.lower (g.parameter (1 - trim))) < 0
    else 0 < normal (1, deriv g.lower (g.parameter trim))
  neighborhood : Set (ℝ × ℝ)
  neighborhood_open : IsOpen neighborhood
  graph_mem_neighborhood :
    (g.parameter (if terminal then 1 - trim else trim),
      g.lower (g.parameter (if terminal then 1 - trim else trim))) ∈ neighborhood
  cap_separated : ∀ q ∈ D.graphCapObstacle region chart B R g.frame ∩ neighborhood,
    normal (q - (g.parameter (if terminal then 1 - trim else trim),
      g.lower (g.parameter (if terminal then 1 - trim else trim)))) ≤ 0
  length : ℝ
  length_mem : length ∈ Ioo (0 : ℝ) 1
  chord_map : ∀ u : ℝ,
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) + u • direction) =
        (((B (D.edgeEndpoint e terminal)).face sector).boundary 0).map
          (if radialEdge = 1 then 1 - u else u)
  chord_image :
    (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) + u • direction)) ''
        Icc (0 : ℝ) 1 = (((B (D.edgeEndpoint e terminal)).face sector).boundary 0).map '' Icc (0 : ℝ) 1
  length_bounds : ∀ u ∈ Icc (0 : ℝ) length,
    chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) + u • direction ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).target ∧
    (g.frame (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) +
      u • direction)).1 ∈ Ioo g.tubeLeft g.tubeRight ∧
    |(g.frame (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) +
      u • direction)).2 - g.lower
        (g.frame (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) +
          u • direction)).1| < g.tubeWidth ∧
    (0 < u → (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) + u • direction) ∈
        connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)

section Construction

variable
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
      (fun s => chart (region p s)))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hsector : ∀ p i, (P p).sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))
    (hclosed : ∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (e : D.EdgeIndex) (R : D.regions) (hR : R = D.regionLeft e ∨ R = D.regionRight e)

include hdisjoint hsector hclosed hR



theorem exists_capGraphEndpoint {a b : ℝ} (hab : a ≤ b)
    (g : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b)
    (terminal : Bool) (trim : ℝ)
    (hendpoint : (if terminal then b else a) = (if terminal then 1 - trim else trim))
    (hmatch : trim ∈ Ioo (0 : ℝ) (1 / 3) ∧
      ∃ (i j : Bool × Bool) (k : Fin 3), i ≠ j ∧ (k = 1 ∨ k = 2) ∧
        (((B (D.edgeEndpoint e terminal)).face i).boundary k).map '' Icc (0 : ℝ) 1 =
          D.edgeFromEndpoint e terminal '' Icc 0 trim ∧
        (((B (D.edgeEndpoint e terminal)).face j).boundary k).map '' Icc (0 : ℝ) 1 =
          D.edgeFromEndpoint e terminal '' Icc 0 trim ∧
        ∀ s, s = i ∨ s = j →
          (((B (D.edgeEndpoint e terminal)).face s).boundary k).map 0 =
            (D.edgeEndpoint e terminal : M) ∧
          (((B (D.edgeEndpoint e terminal)).face s).boundary k).map 1 =
            D.edgeFromEndpoint e terminal trim ∧
          ∃ J : OpenPartialHomeomorph ℝ ℝ,
            J (B (D.edgeEndpoint e terminal)).scale = trim ∧
            Icc 0 (B (D.edgeEndpoint e terminal)).scale ⊆ J.source ∧
            StrictMonoOn J J.source ∧ ContDiffOn ℝ ∞ J J.source ∧
            ContDiffOn ℝ ∞ J.symm J.target ∧
            ∀ u ∈ Icc 0 (B (D.edgeEndpoint e terminal)).scale,
              D.edgeFromEndpoint e terminal (J u) =
                (P (D.edgeEndpoint e terminal)).sectorCoordinates s
                  (if k = 1 then (0, u) else (u, 0))) :
    Nonempty (D.CapGraphEndpoint P region chart B e R g terminal trim) := by
  obtain ⟨htrim, i, j, k, hij, hk, hi, hj, hparameters⟩ := hmatch
  have htI : (if terminal then 1 - trim else trim) ∈ Icc a b := by
    rw [← hendpoint]
    cases terminal
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
  have htG := g.interval_source htI
  have htube : g.parameter (if terminal then 1 - trim else trim) ∈ Ioo g.tubeLeft g.tubeRight := by
    rw [← hendpoint]
    cases terminal
    · exact (g.endpoints_mem_tube hab).1
    · exact (g.endpoints_mem_tube hab).2
  have hparameters' (s : Bool × Bool) (hs : s = i ∨ s = j) :
      ∃ J : OpenPartialHomeomorph ℝ ℝ,
        J (B (D.edgeEndpoint e terminal)).scale = trim ∧
        Icc 0 (B (D.edgeEndpoint e terminal)).scale ⊆ J.source ∧
        StrictMonoOn J J.source ∧ ContDiffOn ℝ ∞ J J.source ∧
        ∀ u ∈ Icc 0 (B (D.edgeEndpoint e terminal)).scale,
          D.edgeFromEndpoint e terminal (J u) =
            (P (D.edgeEndpoint e terminal)).sectorCoordinates s
              (if k = 1 then (0, u) else (u, 0)) := by
    obtain ⟨J, hJ, hsrc, hmono, hsm, _, hcurve⟩ := (hparameters s hs).2.2
    exact ⟨J, hJ, hsrc, hmono, hsm, hcurve⟩
  obtain ⟨s, d, ℓ, W, ρ, hs, hsR, hd, hdne, hbase, htrans, hnormal, hsign,
    hW, hmem, hsep, hρ, hchord, himage, hlength⟩ :=
    D.exists_incident_cap_chord_transversal P region chart B hdisjoint hsector hclosed
      (D.edgeEndpoint e terminal) e terminal ⟨htrim.1, htrim.2.trans (by norm_num)⟩ hij k hk
      (fun s hs => (hparameters s hs).2.1) hparameters' R hR
      g.frame g.parameter g.parameter_smooth g.lower_smooth g.source_chart g.graph_coordinates
      htG (g.positive_projection _ htI) htube g.tube_width_pos
      (fun y hy z hz => (g.tube y hy z hz).2.2.1)
  refine ⟨{
    sector := s
    radialEdge := k
    radialEdge_valid := hk
    sector_region := hsR
    endpoint_parameter := hendpoint
    radial_image := ?_
    radial_start := (hparameters s hs).1
    radial_end := (hparameters s hs).2.1
    direction := d
    direction_eq := hd
    direction_ne_zero := hdne
    chord_base := hbase
    transverse := htrans
    normal := ℓ
    normal_cut := hnormal
    normal_tangent := ?_
    neighborhood := W
    neighborhood_open := hW
    graph_mem_neighborhood := hmem
    cap_separated := hsep
    length := ρ
    length_mem := hρ
    chord_map := hchord
    chord_image := himage
    length_bounds := hlength }⟩
  · rcases hs with rfl | rfl
    · exact hi
    · exact hj
  · cases terminal <;> exact hsign

section Subdivision

variable (cut : Bool → ℝ)
    (hmatch : ∀ terminal : Bool, cut terminal ∈ Ioo (0 : ℝ) (1 / 3) ∧
      ∃ (i j : Bool × Bool) (k : Fin 3), i ≠ j ∧ (k = 1 ∨ k = 2) ∧
        (((B (D.edgeEndpoint e terminal)).face i).boundary k).map '' Icc (0 : ℝ) 1 =
          D.edgeFromEndpoint e terminal '' Icc 0 (cut terminal) ∧
        (((B (D.edgeEndpoint e terminal)).face j).boundary k).map '' Icc (0 : ℝ) 1 =
          D.edgeFromEndpoint e terminal '' Icc 0 (cut terminal) ∧
        ∀ s, s = i ∨ s = j →
          (((B (D.edgeEndpoint e terminal)).face s).boundary k).map 0 =
            (D.edgeEndpoint e terminal : M) ∧
          (((B (D.edgeEndpoint e terminal)).face s).boundary k).map 1 =
            D.edgeFromEndpoint e terminal (cut terminal) ∧
          ∃ J : OpenPartialHomeomorph ℝ ℝ,
            J (B (D.edgeEndpoint e terminal)).scale = cut terminal ∧
            Icc 0 (B (D.edgeEndpoint e terminal)).scale ⊆ J.source ∧
            StrictMonoOn J J.source ∧ ContDiffOn ℝ ∞ J J.source ∧
            ContDiffOn ℝ ∞ J.symm J.target ∧
            ∀ u ∈ Icc 0 (B (D.edgeEndpoint e terminal)).scale,
              D.edgeFromEndpoint e terminal (J u) =
                (P (D.edgeEndpoint e terminal)).sectorCoordinates s
                  (if k = 1 then (0, u) else (u, 0)))
    (S : D.OrientedEdgeGraphSubdivision e R
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (cut false) (1 - cut true))

include hmatch



theorem exists_capGraphEndpoint_pair :
    Nonempty
      (D.CapGraphEndpoint P region chart B e R (S.piece S.firstPiece) false (cut false) ×
        D.CapGraphEndpoint P region chart B e R (S.piece S.lastPiece) true (cut true)) := by
  obtain ⟨L⟩ := D.exists_capGraphEndpoint P region chart B hdisjoint hsector hclosed e R hR
    (S.cut_lt S.firstPiece).le (S.piece S.firstPiece) false (cut false)
    (by simpa only [Bool.false_eq_true, ite_false, S.firstPiece_castSucc] using S.cut_first)
    (hmatch false)
  obtain ⟨R⟩ := D.exists_capGraphEndpoint P region chart B hdisjoint hsector hclosed e R hR
    (S.cut_lt S.lastPiece).le (S.piece S.lastPiece) true (cut true)
    (by simpa only [ite_true, S.lastPiece_succ] using S.cut_last) (hmatch true)
  exact ⟨L, R⟩



theorem exists_cap_attached_cutChain :
    ∃ (L : D.CapGraphEndpoint P region chart B e R (S.piece S.firstPiece) false (cut false))
      (T : D.CapGraphEndpoint P region chart B e R (S.piece S.lastPiece) true (cut true)),
      Nonempty (S.CutChain L.direction T.direction) := by
  obtain ⟨L, T⟩ := D.exists_capGraphEndpoint_pair P region chart B hdisjoint hsector hclosed
    e R hR cut hmatch S
  exact ⟨L, T, S.exists_cutChain (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
    L.direction T.direction L.transverse T.transverse⟩

end Subdivision

end Construction

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
