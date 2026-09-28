import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapGluing

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
  (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
  (region : D.vertices → Bool × Bool → D.regions)
  (caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => (chart (region p s) : M)))
  (S : ∀ p : D.IncidentEdgeIndex,
    D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
      (cut p.1.2 false) (1 - cut p.1.2 true))
  (L : ∀ p, D.CapGraphEndpoint P region (fun R => (chart R : M)) caps p.1.2 p.1.1
    ((S p).piece (S p).firstPiece) false (cut p.1.2 false))
  (T : ∀ p, D.CapGraphEndpoint P region (fun R => (chart R : M)) caps p.1.2 p.1.1
    ((S p).piece (S p).lastPiece) true (cut p.1.2 true))
  (K : ∀ p, (S p).CutChain (L p).direction (T p).direction) {δ r : ℝ}
  (bands : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)
  (havoid : ∀ p i, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
    ((K p).graphCuts i).coordinates ((S p).piece i).parameter.open_target
      ((S p).piece i).lower_smooth (t, z) ∉
        D.graphCapObstacle region (fun R => (chart R : M)) caps p.1.1 ((S p).piece i).frame)

include havoid

theorem left_attachment_subset_interior_fittedRegionCollar (hr : r ≤ 1)
    (p : D.IncidentEdgeIndex) :
    (L p).openChordSegment r ⊆
      interior (D.fittedRegionCollar chart cut S K bands caps region p.1.1) := by
  apply ((K p).left_attachment_subset_interior (L p) (T p) hr
    (bands p (S p).firstPiece) (havoid p (S p).firstPiece)).trans
  apply interior_mono
  apply union_subset
  · intro q hq
    exact Or.inl (mem_iUnion.mpr
      ⟨⟨(D.edgeEndpoint p.1.2 false, (L p).sector), (L p).sector_region⟩, hq⟩)
  · intro q hq
    exact Or.inr (mem_iUnion.mpr ⟨⟨⟨p, (S p).firstPiece⟩, rfl⟩, hq⟩)

theorem right_attachment_subset_interior_fittedRegionCollar (hr : r ≤ 1)
    (p : D.IncidentEdgeIndex) :
    (T p).openChordSegment r ⊆
      interior (D.fittedRegionCollar chart cut S K bands caps region p.1.1) := by
  apply ((K p).right_attachment_subset_interior (L p) (T p) hr
    (bands p (S p).lastPiece) (havoid p (S p).lastPiece)).trans
  apply interior_mono
  apply union_subset
  · intro q hq
    exact Or.inl (mem_iUnion.mpr
      ⟨⟨(D.edgeEndpoint p.1.2 true, (T p).sector), (T p).sector_region⟩, hq⟩)
  · intro q hq
    exact Or.inr (mem_iUnion.mpr ⟨⟨⟨p, (S p).lastPiece⟩, rfl⟩, hq⟩)

theorem openChordAttachment_subset_interior_fittedRegionCollar
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
    (hr : r ≤ 1) (R : D.regions) (p : D.vertices) (s : Bool × Bool)
    (terminal : Bool) (hsR : region p s = R) :
    (caps p).openChordAttachment (chartDiskBoundaryUnion D.centers D.radius) s terminal r ⊆
      interior (D.fittedRegionCollar chart cut S K bands caps region R) := by
  classical
  by_cases htip : (((caps p).face s).boundary 0).map (if terminal then 1 else 0) ∈
      chartDiskBoundaryUnion D.centers D.radius
  · have hk : (if terminal then 1 else 2 : Fin 3) = 1 ∨
        (if terminal then 1 else 2 : Fin 3) = 2 := by cases terminal <;> simp
    have htiprad : (((caps p).face s).boundary (if terminal then 1 else 2)).map 1 ∈
        chartDiskBoundaryUnion D.centers D.radius := by
      rwa [← (caps p).chord_endpoint_eq_radial_tip s terminal]
    obtain ⟨e, b, hp, heq, hincident, hunique⟩ := D.exists_cap_radial_attachment P caps region
      hdisjoint hlocal hsector hclosed cut hcut hmatch p s (if terminal then 1 else 2) hk htiprad
    have hR : R = D.regionLeft e ∨ R = D.regionRight e := hsR ▸ hincident
    let a : D.IncidentEdgeIndex := ⟨(R, e), hR⟩
    subst p
    have hcutK : D.edgeFromEndpoint e b (cut e b) ∈ chartDiskBoundaryUnion D.centers D.radius :=
      heq ▸ htiprad
    cases b
    · have hcap : D.edgeFromEndpoint e false (cut e false) ∈
          ((caps (D.edgeEndpoint e false)).face (L a).sector).carrier :=
        ((caps (D.edgeEndpoint e false)).face (L a).sector).isClosed_carrier.frontier_subset
          (((caps (D.edgeEndpoint e false)).face (L a).sector).boundary_image_subset_frontier
            (L a).radialEdge ⟨1, by norm_num, (L a).radial_end⟩)
      have hselected : (L a).sector = s :=
        (hunique _ _ hcap ((L a).sector_region.trans hsR.symm)).2
      have hedge : (L a).radialEdge = (if terminal then 1 else 2) := by
        apply (caps (D.edgeEndpoint e false)).radial_tip_injective s (L a).radialEdge_valid hk
        simpa only [hselected] using (L a).radial_end.trans heq.symm
      have horientation : decide ((L a).radialEdge = 1) = terminal := by
        rw [hedge]
        cases terminal <;> decide
      have hsame := (L a).openChordSegment_eq_openChordAttachment
        (chartDiskBoundaryUnion D.centers D.radius) r hcutK
      rw [hselected, horientation] at hsame
      rw [← hsame]
      exact D.left_attachment_subset_interior_fittedRegionCollar chart cut P region caps S L T K
        bands havoid hr a
    · have hcap : D.edgeFromEndpoint e true (cut e true) ∈
          ((caps (D.edgeEndpoint e true)).face (T a).sector).carrier :=
        ((caps (D.edgeEndpoint e true)).face (T a).sector).isClosed_carrier.frontier_subset
          (((caps (D.edgeEndpoint e true)).face (T a).sector).boundary_image_subset_frontier
            (T a).radialEdge ⟨1, by norm_num, (T a).radial_end⟩)
      have hselected : (T a).sector = s :=
        (hunique _ _ hcap ((T a).sector_region.trans hsR.symm)).2
      have hedge : (T a).radialEdge = (if terminal then 1 else 2) := by
        apply (caps (D.edgeEndpoint e true)).radial_tip_injective s (T a).radialEdge_valid hk
        simpa only [hselected] using (T a).radial_end.trans heq.symm
      have horientation : decide ((T a).radialEdge = 1) = terminal := by
        rw [hedge]
        cases terminal <;> decide
      have hsame := (T a).openChordSegment_eq_openChordAttachment
        (chartDiskBoundaryUnion D.centers D.radius) r hcutK
      rw [hselected, horientation] at hsame
      rw [← hsame]
      exact D.right_attachment_subset_interior_fittedRegionCollar chart cut P region caps S L T K
        bands havoid hr a
  · simp only [ChartCircleArrangementVertexPatch.VertexCapFaces.openChordAttachment, if_neg htip]
    exact empty_subset _

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
