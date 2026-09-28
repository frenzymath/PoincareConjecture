import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Interfaces
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Attachments
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CutGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  (region : D.vertices → Bool × Bool → D.regions)
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun i => (chart (region p i) : M)))
  (L : ∀ p, D.CapGraphEndpoint P region (fun R => (chart R : M)) caps p.1.2 p.1.1
    ((S p).piece (S p).firstPiece) false (cut p.1.2 false))
  (T : ∀ p, D.CapGraphEndpoint P region (fun R => (chart R : M)) caps p.1.2 p.1.1
    ((S p).piece (S p).lastPiece) true (cut p.1.2 true))
  (K : ∀ p, (S p).CutChain (L p).direction (T p).direction) {δ r : ℝ}
  (B : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)

theorem frontier_graphBandsInRegion_subset (hr : r ≤ 1)
    (hseparate : ∀ p (i j : Fin (S p).count), i.succ = j.castSucc →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ z w : ℝ, |z| < δ → |w| < δ →
          ((S p).piece i).strip ((K p).graphCuts i) (t, z) =
            ((S p).piece j).strip ((K p).graphCuts j) (s, w) → t = 1 ∧ s = 0)
    (R : D.regions) :
    frontier (D.graphBandsInRegion chart cut S K B R) ⊆
      chartDiskBoundaryUnion D.centers D.radius ∪ D.vertexCapChordsInRegion caps region R ∪
        D.graphBandTopsInRegion chart cut S K B R := by
  rw [D.graphBandsInRegion_eq_iUnion_chains]
  intro q hq
  obtain ⟨p, hp⟩ := mem_iUnion.mp
    (Poincare.Topology.frontier_iUnion_subset_iUnion_frontier_of_isClosed
      (fun p : {p : D.IncidentEdgeIndex // p.1.1 = R} => ⋃ i, (B p.1 i).faces.carrier)
      (fun p => isClosed_iUnion_of_finite (fun i => (B p.1 i).faces.isClosed_carrier)) hq)
  rcases (K p.1).frontier_iUnion_band_carrier_subset (B p.1) (hseparate p.1) hp with
    ((hedge | htop) | hleft) | hright
  · left; left
    rw [← D.boundary_cover]
    apply mem_iUnion.mpr
    refine ⟨p.1.1.2, image_mono ?_ hedge⟩
    apply Icc_subset_Icc
    · simpa only [(S p.1).cut_first] using ((S p.1).cut_mem 0).1.le
    · simpa only [(S p.1).cut_last] using ((S p.1).cut_mem (Fin.last _)).2.le
  · obtain ⟨i, hi⟩ := mem_iUnion.mp htop
    exact Or.inr (mem_iUnion.mpr ⟨⟨⟨p.1, i⟩, p.2⟩, hi⟩)
  · have heq : (B p.1 (S p.1).firstPiece).faces.leftCut = (L p.1).chordSegment r := by
      simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
        OpenPartialHomeomorph.symm_symm, OrientedEdgeGraphSubdivision.firstPiece_castSucc,
        OrientedEdgeGraphSubdivision.cut_first, (K p.1).first,
        CapGraphEndpoint.chordSegment, edgeFromEndpoint, Bool.false_eq_true, ite_false] using
        (B p.1 (S p.1).firstPiece).leftCut_eq_ray ((S p.1).cut_lt (S p.1).firstPiece).le
    exact Or.inl (Or.inr (mem_iUnion.mpr
      ⟨⟨(D.edgeEndpoint p.1.1.2 false, (L p.1).sector), (L p.1).sector_region.trans p.2⟩,
        (L p.1).chordSegment_subset_chord hr (heq ▸ hleft)⟩))
  · have heq : (B p.1 (S p.1).lastPiece).faces.rightCut = (T p.1).chordSegment r := by
      simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
        OpenPartialHomeomorph.symm_symm, OrientedEdgeGraphSubdivision.lastPiece_succ,
        OrientedEdgeGraphSubdivision.cut_last, (K p.1).last,
        CapGraphEndpoint.chordSegment, edgeFromEndpoint, ite_true] using
        (B p.1 (S p.1).lastPiece).rightCut_eq_ray ((S p.1).cut_lt (S p.1).lastPiece).le
    exact Or.inl (Or.inr (mem_iUnion.mpr
      ⟨⟨(D.edgeEndpoint p.1.1.2 true, (T p.1).sector), (T p.1).sector_region.trans p.2⟩,
        (T p.1).chordSegment_subset_chord hr (heq ▸ hright)⟩))

variable
  (hseparate : ∀ p (i j : Fin (S p).count), i.succ = j.castSucc →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        ((S p).piece i).strip ((K p).graphCuts i) (t, z) =
          ((S p).piece j).strip ((K p).graphCuts j) (s, w) → t = 1 ∧ s = 0)
  (hcaps : ∀ p i, ((caps p).face i).carrier ⊆ closure (connectedComponentIn
    (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))

include hseparate hcaps

theorem frontier_fittedRegionCollar_subset_chords (hr : r ≤ 1) (R : D.regions) :
    frontier (D.fittedRegionCollar chart cut S K B caps region R) ⊆
      chartDiskBoundaryUnion D.centers D.radius ∪ D.vertexCapChordsInRegion caps region R ∪
        D.graphBandTopsInRegion chart cut S K B R := by
  intro q hq
  rcases frontier_union_subset _ _ hq with hcap | hband
  · exact Or.inl (D.frontier_vertexCapsInRegion_subset caps region hcaps R hcap.1)
  · exact D.frontier_graphBandsInRegion_subset chart cut S region caps L T K B
      hr hseparate R hband.2

theorem frontier_fittedRegionCollar_subset
    (havoid : ∀ p i, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
      ((K p).graphCuts i).coordinates ((S p).piece i).parameter.open_target
        ((S p).piece i).lower_smooth (t, z) ∉
          D.graphCapObstacle region (fun R => (chart R : M)) caps p.1.1 ((S p).piece i).frame)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (hsector : ∀ p i, (P p).sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))
    (hclosed : ∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (hcut : ∀ a b, cut a b ∈ Ioo (0 : ℝ) 1)
    (hmatch : ∀ a b, ∃ (i j : Bool × Bool) (k : Fin 3), i ≠ j ∧ (k = 1 ∨ k = 2) ∧
      (((caps (D.edgeEndpoint a b)).face i).boundary k).map '' Icc (0 : ℝ) 1 =
        D.edgeFromEndpoint a b '' Icc 0 (cut a b) ∧
      ∀ s, s = i ∨ s = j → (((caps (D.edgeEndpoint a b)).face s).boundary k).map 1 =
        D.edgeFromEndpoint a b (cut a b))
    (hr : r ≤ 1) (R : D.regions) :
    frontier (D.fittedRegionCollar chart cut S K B caps region R) ⊆
      chartDiskBoundaryUnion D.centers D.radius ∪
        D.fittedRegionInterface chart cut S K B caps region R := by
  intro q hq
  rcases D.frontier_fittedRegionCollar_subset_chords chart cut S region caps L T K B
    hseparate hcaps hr R hq with (hK | hchord) | htop
  · exact Or.inl hK
  · obtain ⟨a, ha⟩ := mem_iUnion.mp hchord
    rcases (caps a.1.1).chord_subset_remainder_attachments
      (chartDiskBoundaryUnion D.centers D.radius) a.1.2 r ha with
        (hK | hrem) | hattach
    · exact Or.inl hK
    · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨a, hrem⟩))
    · have hc (terminal : Bool) :=
        D.openChordAttachment_subset_interior_fittedRegionCollar chart cut P region caps
          S L T K B havoid hdisjoint hlocal hsector hclosed hcut hmatch hr R
            a.1.1 a.1.2 terminal a.2
      exact False.elim (hq.2 (hattach.elim (fun h => hc false h) (fun h => hc true h)))
  · exact Or.inr (Or.inr htop)

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
