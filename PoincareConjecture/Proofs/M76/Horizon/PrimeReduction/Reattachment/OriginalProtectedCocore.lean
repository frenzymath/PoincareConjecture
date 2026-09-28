import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedBallProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.MarkedProductInteriorChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreWindow







set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Cube" => Set.prod (Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1)
local notation "OpenCube" => Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-1 : ℝ) 1)

theorem HamiltonMarkedProtectedBall.exists_original_cocore_window_of_isClosed
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 2)
    (hS : IsClosed S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    ∃ (p : P3 → LatticeHandleAmbient ι κ L)
      (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
      (J : SimplicialComplex ℝ V3),
      PolyhedralPLInCharts e p Cube ∧ InjOn p Cube ∧ p '' Cube = D ∧
      Q.source = interior D ∧ Q.target = markedProductCoordinates ⁻¹' OpenCube ∧
      (∀ y, Q.symm y = p (markedProductCoordinates y)) ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      J.faces.Finite ∧ J.space ⊆ Q.target ∧ Convex ℝ J.space ∧
      MapsTo Q.symm J.space (interior (latticeHandleDomain ι κ L)) ∧
      (∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
        (markedProductCoordinates x).2 ∈ Ioo (-(1/2 : ℝ)) (1/2) →
          x ∈ interior J.space) ∧
      (∀ z ∈ Cube, z.2 ∈ Ioo (-(1/2 : ℝ)) (1/2) → p z ∈ S →
        markedProductCoordinates.symm z ∈ interior J.space) ∧
      (∀ z ∈ Cube, (|z.1.1| = 1 ∨ |z.1.2| = 1) →
        p z ∈ frontier (latticeHandleDomain ι κ L)) ∧
      MapsTo p OpenCube (interior (latticeHandleDomain ι κ L)) ∧
      (∀ z ∈ Cube, p z ∈ frontier (latticeHandleDomain ι κ L) ↔
        |z.1.1| = 1 ∨ |z.1.2| = 1) := by
  obtain ⟨p,G,hp,_,hpi,himage,hlateral,hboundary,_⟩ :=
    b.exists_original_protected_ball_product he hdim hi
  obtain ⟨Q,hQs,hQt,hQinv,hQ⟩ := exists_marked_product_interior_chart
    he.compatible p hp hpi himage hboundary
  have hmark : D ∩ frontier (latticeHandleDomain ι κ L) =
      hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hzero,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hlat (z : P3) (hz : z ∈ Cube) (hl : |z.1.1| = 1 ∨ |z.1.2| = 1) :
      p z ∈ frontier (latticeHandleDomain ι κ L) :=
    (hmark.symm.subset ((hlateral z hz).mpr hl)).2
  have hvalues (z : P3) (_hz : z ∈ OpenCube) :
      Q.symm (markedProductCoordinates.symm z) = p z := by
    rw [hQinv,markedProductCoordinates.apply_symm_apply]
  have hinner : MapsTo p OpenCube (interior (latticeHandleDomain ι κ L)) := by
    intro z hz
    have ht : markedProductCoordinates.symm z ∈ Q.target := by
      rw [hQt]
      change markedProductCoordinates (markedProductCoordinates.symm z) ∈ OpenCube
      simpa only [markedProductCoordinates.apply_symm_apply] using hz
    have hd : p z ∈ interior D := by
      rw [← hvalues z hz,← hQs]
      exact Q.map_target ht
    exact interior_mono b.subset_domain hd
  obtain ⟨J,hJ,hJQ,hJcv,hJR,hband,hall⟩ := exists_cocore_window_from_lateral_incidence
    hS hSR p hp.continuousOn hlat hinner Q markedProductCoordinates hQt hvalues
  refine ⟨p,Q,J,hp,hpi,himage,hQs,hQt,hQinv,hQ,hJ,hJQ,hJcv,hJR,hband,hall,hlat,hinner,?_⟩
  intro z hz
  constructor
  · intro hfront
    exact (hlateral z hz).mp (hmark.subset ⟨himage.subset ⟨z,hz,rfl⟩,hfront⟩)
  · exact hlat z hz

theorem HamiltonMarkedProtectedBall.exists_original_cocore_window
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 2)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    ∃ (p : P3 → LatticeHandleAmbient ι κ L)
      (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
      (J : SimplicialComplex ℝ V3),
      PolyhedralPLInCharts e p Cube ∧ InjOn p Cube ∧ p '' Cube = D ∧
      Q.source = interior D ∧ Q.target = markedProductCoordinates ⁻¹' OpenCube ∧
      (∀ y, Q.symm y = p (markedProductCoordinates y)) ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      J.faces.Finite ∧ J.space ⊆ Q.target ∧ Convex ℝ J.space ∧
      MapsTo Q.symm J.space (interior (latticeHandleDomain ι κ L)) ∧
      (∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
        (markedProductCoordinates x).2 ∈ Ioo (-(1/2 : ℝ)) (1/2) →
          x ∈ interior J.space) ∧
      (∀ z ∈ Cube, z.2 ∈ Ioo (-(1/2 : ℝ)) (1/2) → p z ∈ S →
        markedProductCoordinates.symm z ∈ interior J.space) ∧
      (∀ z ∈ Cube, (|z.1.1| = 1 ∨ |z.1.2| = 1) →
        p z ∈ frontier (latticeHandleDomain ι κ L)) ∧
      MapsTo p OpenCube (interior (latticeHandleDomain ι κ L)) := by
  obtain ⟨p,Q,J,hp,hpi,himage,hQs,hQt,hQinv,hQ,hJ,hJQ,hJcv,hJR,hband,hall,hlat,hinner,_⟩ :=
    b.exists_original_cocore_window_of_isClosed he hdim hi s.isCompact.isClosed hSR
  exact ⟨p,Q,J,hp,hpi,himage,hQs,hQt,hQinv,hQ,hJ,hJQ,hJcv,hJR,hband,hall,hlat,hinner⟩

end PoincareConjecture.M76
