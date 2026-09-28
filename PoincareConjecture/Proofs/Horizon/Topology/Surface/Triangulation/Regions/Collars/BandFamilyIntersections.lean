


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CrossRegionBands









set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u

private theorem sigma_pairwise_of_fibers {α : Type*} {β : α → Type*}
    {R : (Σ a, β a) → (Σ a, β a) → Prop}
    (hsame : ∀ a, ∀ v w : β a, v ≠ w → R ⟨a, v⟩ ⟨a, w⟩)
    (hdifferent : ∀ a b, a ≠ b → ∀ v : β a, ∀ w : β b,
      R ⟨a, v⟩ ⟨b, w⟩) :
    ∀ i j, i ≠ j → R i j := by
  rintro ⟨a, v⟩ ⟨b, w⟩ hne
  by_cases h : a = b
  · subst b
    exact hsame a v w (fun he => hne (congrArg (Sigma.mk a) he))
  · exact hdifferent a b h v w

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



private def bandFamilyRelation :
    (Σ a : D.IncidentGraphPieceIndex chart cut S,
      Fin (B a.1 a.2).faces.interface.count × Bool) →
    (Σ a : D.IncidentGraphPieceIndex chart cut S,
      Fin (B a.1 a.2).faces.interface.count × Bool) → Prop :=
  Sigma.uncurry fun a v => Sigma.uncurry fun b w =>
    CoordinateTriangleBoundaryIntersection
      ((B a.1 a.2).faces.faceCoordinates v)
      ((B b.1 b.2).faces.faceCoordinates w)
      ((B a.1 a.2).faces.faceBasis v)
      ((B b.1 b.2).faces.faceBasis w)




theorem band_family_faces_coordinate_intersection
    (hcut : ∀ e t, cut e t ∈ Ioo (0 : ℝ) (1 / 3))
    (hstripAdjacent : ∀ p (i j : Fin (S p).count), i.succ = j.castSucc →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ z w : ℝ, |z| < δ → |w| < δ →
          ((S p).piece i).strip ((K p).graphCuts i) (t, z) =
            ((S p).piece j).strip ((K p).graphCuts j) (s, w) → t = 1 ∧ s = 0)
    (hstripSeparate : ∀ i j : D.IncidentGraphPieceIndex chart cut S,
      D.IncidentGraphPiecesSeparated chart cut S i j → Disjoint
        (((S i.1).piece i.2).strip ((K i.1).graphCuts i.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ))
        (((S j.1).piece j.2).strip ((K j.1).graphCuts j.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ)))
    (hbandsclosure : ∀ p i, (B p i).faces.carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1))
    (hzero : ∀ p i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 ≤ z → z < δ →
      (((S p).piece i).strip ((K p).graphCuts i) (t, z) ∈
        chartDiskBoundaryUnion D.centers D.radius ↔ z = 0))
    (i j : Σ a : D.IncidentGraphPieceIndex chart cut S,
      Fin (B a.1 a.2).faces.interface.count × Bool) (hne : i ≠ j) :
    bandFamilyRelation D chart cut S K B i j := by
  refine sigma_pairwise_of_fibers
    (β := fun a : D.IncidentGraphPieceIndex chart cut S =>
      Fin (B a.1 a.2).faces.interface.count × Bool)
    (R := bandFamilyRelation D chart cut S K B) ?_ ?_ i j hne
  · intro a v w hvw
    exact (B a.1 a.2).faces.face_coordinate_intersection v w hvw
  · intro a b hab v w
    by_cases hregion : a.1.1.1 = b.1.1.1
    · exact D.incident_band_faces_coordinate_intersection chart cut S K B
        hstripAdjacent hstripSeparate a b hab hregion v w
    · exact D.cross_region_band_faces_coordinate_intersection chart cut S K B
        hcut hbandsclosure hzero a b hregion v w

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
