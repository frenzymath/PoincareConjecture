import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.ChordRemainders
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Affine.Lines
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.OuterFaces

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

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
  {dLeft dRight : D.IncidentEdgeIndex → EuclideanSpace ℝ (Fin 2)}
  (K : ∀ p, (S p).CutChain (dLeft p) (dRight p)) {δ r : ℝ}
  (B : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)

def graphBandTopsInRegion (R : D.regions) : Set M :=
  ⋃ a : {a : D.IncidentGraphPieceIndex chart cut S // a.1.1.1 = R},
    (B a.1.1 a.1.2).faces.polygonalTop

omit [T2Space M] in
theorem isCompact_graphBandTopsInRegion (R : D.regions) :
    IsCompact (D.graphBandTopsInRegion chart cut S K B R) :=
  isCompact_iUnion (fun a => (B a.1.1 a.1.2).faces.isCompact_polygonalTop)

omit [T2Space M] in
theorem graphBandTopsInRegion_subset_region
    (hpositive : ∀ p i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 < z → z < δ →
      ((S p).piece i).strip ((K p).graphCuts i) (t, z) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1) (R : D.regions) :
    D.graphBandTopsInRegion chart cut S K B R ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
  intro q hq
  obtain ⟨a, ha⟩ := mem_iUnion.mp hq
  rw [← (B a.1.1 a.1.2).faces.height_graph_image] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  change (B a.1.1 a.1.2).faces.coordinates
    (collarParameterEquiv.symm (t, (B a.1.1 a.1.2).faces.height t)) ∈ _
  rw [(B a.1.1 a.1.2).coordinates_eq]
  simpa only [a.property] using hpositive a.1.1 a.1.2 t ht _
    ((B a.1.1 a.1.2).height_bounds ht).1 ((B a.1.1 a.1.2).height_bounds ht).2

theorem graphBandTopsInRegion_subset_bands (R : D.regions) :
    D.graphBandTopsInRegion chart cut S K B R ⊆ D.graphBandsInRegion chart cut S K B R := by
  apply iUnion_mono
  intro a q hq
  exact (B a.1.1 a.1.2).faces.isClosed_carrier.frontier_subset
    ((B a.1.1 a.1.2).faces.outer_boundaries_subset_frontier (Or.inl (Or.inl (Or.inr hq))))

variable {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (region : D.vertices → Bool × Bool → D.regions)

def fittedRegionInterface (R : D.regions) : Set M :=
  D.vertexCapChordRemainders caps region R r ∪ D.graphBandTopsInRegion chart cut S K B R

omit [T2Space M] in
theorem isCompact_fittedRegionInterface (hr : 0 ≤ r) (R : D.regions) :
    IsCompact (D.fittedRegionInterface chart cut S K B caps region R) :=
  (D.isCompact_vertexCapChordRemainders caps region R hr).union
    (D.isCompact_graphBandTopsInRegion chart cut S K B R)

theorem fittedRegionInterface_subset_collar (hr : 0 ≤ r) (R : D.regions) :
    D.fittedRegionInterface chart cut S K B caps region R ⊆
      D.fittedRegionCollar chart cut S K B caps region R :=
  union_subset_union (D.vertexCapChordRemainders_subset_caps caps region R hr)
    (D.graphBandTopsInRegion_subset_bands chart cut S K B R)

theorem fittedRegionInterface_subset_region
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (hcapRegions : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (hpositive : ∀ p i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 < z → z < δ →
      ((S p).piece i).strip ((K p).graphCuts i) (t, z) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1)
    (hr : 0 < r) (R : D.regions) :
    D.fittedRegionInterface chart cut S K B caps region R ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R :=
  union_subset (D.vertexCapChordRemainders_subset_region caps region hlocal hcapRegions R hr)
    (D.graphBandTopsInRegion_subset_region chart cut S K B hpositive R)

theorem fittedRegionInterface_disjoint_arrangement
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (hcapRegions : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (hpositive : ∀ p i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 < z → z < δ →
      ((S p).piece i).strip ((K p).graphCuts i) (t, z) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1)
    (hr : 0 < r) (R : D.regions) :
    Disjoint (D.fittedRegionInterface chart cut S K B caps region R)
      (chartDiskBoundaryUnion D.centers D.radius) := by
  apply disjoint_left.mpr
  intro q hq hK
  exact connectedComponentIn_subset _ _
    (D.fittedRegionInterface_subset_region chart cut S K B caps region
      hlocal hcapRegions hpositive hr R hq) hK

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

namespace PoincareConjecture.Topology.Surface

open Poincare.Topology.Plane
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

open Poincare.Topology.Plane.Curves

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

omit [T2Space M] in
private theorem inverse_band_coordinates {q : ℝ × ℝ}
    (hq : collarParameterEquiv.symm q ∈ B.faces.band) :
    C.symm (B.faces.coordinates (collarParameterEquiv.symm q)) =
      G.frame.symm (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower q) := by
  have hs := B.faces.band_subset_source hq
  have hsC : G.frame.symm
      (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower q) ∈ C.source := by
    have h := hs.2.2
    change G.frame.symm (collarParameterEquiv (collarParameterEquiv.symm
      (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
        (collarParameterEquiv (collarParameterEquiv.symm q))))) ∈ C.source at h
    simpa only [collarParameterEquiv.apply_symm_apply] using h
  rw [B.faces.coordinates_pair_apply, linearGraphCoordinates_apply,
    collarParameterEquiv.apply_symm_apply, C.left_inv hsC]

omit [T2Space M] in

theorem exists_polygonalTop_chart_lines :
    ∃ lines : List (Plane →ᵃ[ℝ] ℝ), (∀ l ∈ lines, Function.Surjective l) ∧
      C.symm '' B.faces.polygonalTop ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
  let v := fun k : Fin (B.faces.interface.count + 1) => G.frame.symm
    (B.faces.interface.cut k, G.lower (B.faces.interface.cut k) + B.faces.interface.height k)
  apply exists_affine_lines_of_finite_segment_cover
    (fun i : Fin B.faces.interface.count => v i.castSucc) (fun i => v i.succ)
  rintro z ⟨y, hy, rfl⟩
  rw [← B.faces.height_graph_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have ht' := ht
  rw [← B.faces.cut_interval_cover] at ht'
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht'
  refine mem_iUnion.mpr ⟨i, ?_⟩
  have hband : collarParameterEquiv.symm (t, B.faces.height t) ∈ B.faces.band := by
    rw [B.faces.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using
      And.intro ht (And.intro (B.faces.height_pos ht).le (le_refl (B.faces.height t)))
  change C.symm (B.faces.coordinates (collarParameterEquiv.symm (t, B.faces.height t))) ∈ _
  rw [B.inverse_band_coordinates hband]
  have hsegment := (B.faces.interface.pieceCoordinates B.faces.open_domain
    B.faces.smooth_lower i).coordinates_image_upperGraph_eq_segment
      B.faces.open_domain B.faces.smooth_lower
  have hmem : B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
      (t, B.faces.height t) ∈ segment ℝ
        (B.faces.interface.cut i.castSucc,
          G.lower (B.faces.interface.cut i.castSucc) + B.faces.interface.height i.castSucc)
        (B.faces.interface.cut i.succ,
          G.lower (B.faces.interface.cut i.succ) + B.faces.interface.height i.succ) := by
    rw [← hsegment]
    refine ⟨t, hi, ?_⟩
    rw [B.faces.height_eq_upperGraph hi]
  have hmap := mem_image_of_mem G.frame.symm hmem
  change G.frame.symm.toLinearMap.toAffineMap _ ∈
    G.frame.symm.toLinearMap.toAffineMap '' _ at hmap
  rw [image_segment] at hmap
  exact hmap

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {r : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)

theorem exists_chord_chart_line (i : Bool × Bool) :
    ∃ l : Plane →ᵃ[ℝ] ℝ, Function.Surjective l ∧
      (chartAt Plane (x i)) '' (((B.face i).boundary 0).map '' Icc (0 : ℝ) 1) ⊆ {z | l z = 0} := by
  rw [B.chart_chord_image i, affineSegment_eq_segment]
  exact exists_affine_line_containing_segment _ _

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  (chart : D.regions → D.centers) (cut : D.EdgeIndex → Bool → ℝ)
  (S : ∀ p : D.IncidentEdgeIndex,
    D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt Plane (chart p.1.1 : M)).symm (cut p.1.2 false) (1 - cut p.1.2 true))
  {dLeft dRight : D.IncidentEdgeIndex → Plane}
  (K : ∀ p, (S p).CutChain (dLeft p) (dRight p)) {δ r : ℝ}
  (B : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)

omit [T2Space M] in
theorem exists_graphBandTopsInRegion_chart_lines (R : D.regions) :
    ∃ lines : List (Plane →ᵃ[ℝ] ℝ), (∀ l ∈ lines, Function.Surjective l) ∧
      (chartAt Plane (chart R : M)) '' D.graphBandTopsInRegion chart cut S K B R ⊆
        ⋃ l ∈ lines, {z | l z = 0} := by
  rw [graphBandTopsInRegion, image_iUnion]
  apply exists_affine_lines_iUnion
  intro a
  simpa only [OpenPartialHomeomorph.symm_symm, a.property] using
    (B a.1.1 a.1.2).exists_polygonalTop_chart_lines

variable {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (region : D.vertices → Bool × Bool → D.regions)

omit [T2Space M] in
theorem exists_vertexCapChordsInRegion_chart_lines
    (hx : ∀ p i, x p i = (chart (region p i) : M)) (R : D.regions) :
    ∃ lines : List (Plane →ᵃ[ℝ] ℝ), (∀ l ∈ lines, Function.Surjective l) ∧
      (chartAt Plane (chart R : M)) '' D.vertexCapChordsInRegion caps region R ⊆
        ⋃ l ∈ lines, {z | l z = 0} := by
  rw [vertexCapChordsInRegion, image_iUnion]
  apply exists_affine_lines_iUnion
  intro a
  obtain ⟨l, hl, hcover⟩ := (caps a.1.1).exists_chord_chart_line a.1.2
  refine ⟨[l], by simpa using hl, ?_⟩
  simp only [List.mem_singleton, iUnion_iUnion_eq_left]
  simpa only [hx, a.property] using hcover

omit [T2Space M] in

theorem exists_fittedRegionInterface_chart_lines
    (hx : ∀ p i, x p i = (chart (region p i) : M)) (hr : 0 ≤ r) (R : D.regions) :
    ∃ lines : List (Plane →ᵃ[ℝ] ℝ), (∀ l ∈ lines, Function.Surjective l) ∧
      (chartAt Plane (chart R : M)) '' D.fittedRegionInterface chart cut S K B caps region R ⊆
        ⋃ l ∈ lines, {z | l z = 0} := by
  obtain ⟨lc, hc, hcap⟩ := D.exists_vertexCapChordsInRegion_chart_lines chart caps region hx R
  obtain ⟨lb, hb, hband⟩ := D.exists_graphBandTopsInRegion_chart_lines chart cut S K B R
  refine ⟨lc ++ lb, ?_, ?_⟩
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hc l hl
    · exact hb l hl
  · have hrem : D.vertexCapChordRemainders caps region R r ⊆
        D.vertexCapChordsInRegion caps region R :=
      iUnion_mono (fun a => (caps a.1.1).chordRemainder_subset_chord _ a.1.2 hr)
    rw [fittedRegionInterface, image_union]
    apply union_subset
    · intro z hz
      obtain ⟨l, hl⟩ := mem_iUnion.mp (hcap (image_mono hrem hz))
      obtain ⟨hl, hz⟩ := mem_iUnion.mp hl
      exact mem_iUnion.mpr ⟨l, mem_iUnion.mpr ⟨List.mem_append_left _ hl, hz⟩⟩
    · intro z hz
      obtain ⟨l, hl⟩ := mem_iUnion.mp (hband hz)
      obtain ⟨hl, hz⟩ := mem_iUnion.mp hl
      exact mem_iUnion.mpr ⟨l, mem_iUnion.mpr ⟨List.mem_append_right _ hl, hz⟩⟩

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
