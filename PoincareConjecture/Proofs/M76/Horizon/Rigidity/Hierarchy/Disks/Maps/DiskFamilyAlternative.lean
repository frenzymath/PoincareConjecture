import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.HomeomorphicDiskFamilyInstallation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.DiskBoundaryFailure

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "V2" => (Fin 2 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_disk_family_homeomorphic_or_failure_arc
    {ι κ η : Type*} [Fintype η]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
    (j : η → V2 → X0) (hj : ∀ i, PolyhedralPLInCharts e (j i) Disk)
    (hji : ∀ i, Topology.IsEmbedding (fun z : Disk => j i z))
    (hjR : ∀ i, MapsTo (j i) Disk R)
    (hrim : ∀ i, ∀ z : Disk, (z : V2) ∈ sphere (0 : V2) 1 ↔ j i z ∈ frontier R)
    (hdis : Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)))
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hab : alpha < beta) (hbeta : beta < cut + p)
    (ha : cut' < a) (horder : a < b) (hb : b < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (theta : η → C0) (hthird : ∀ i, ∀ z : Disk, hamiltonZeroThirdCircleMap phi (j i z) = theta i)
    (hboundaryEdges : ∀ i, ∀ z ∈ sphere (0 : V2) 1,
      hamiltonZeroCircleMap phi (j i z) ∈ ({(alpha : C0), (beta : C0)} : Set C0) ∨
      hamiltonZeroSecondCircleMap phi (j i z) ∈ ({(a : C0), (b : C0)} : Set C0))
    :
    (∃ (v w : η → V2 → ℝ) (q : η → V2 → X0)
      (E : η → Disk ≃ₜ (Icc alpha beta ×ˢ Icc a b)) (psi : C(H0, H0)),
      (∀ i, FinitePiecewiseAffineOn (v i) Disk) ∧
      (∀ i, FinitePiecewiseAffineOn (w i) Disk) ∧
      (∀ i, (E i).IsFinitePL) ∧
      (∀ i, ∀ z : Disk, (E i z : ℝ × ℝ) = (v i z, w i z)) ∧
      (∀ i, ∀ z ∈ Disk, v i z ∈ Icc alpha beta ∧ w i z ∈ Icc a b) ∧
      (∀ i, PolyhedralPLInCharts d (q i) Disk) ∧
      (∀ i, ∀ z ∈ Disk, Q0 (q i z) = ((theta i, (w i z : C0)), (v i z : C0))) ∧
      (∀ i, InjOn (q i) Disk) ∧
      (∀ i, EqOn (q i) (fun z => hamiltonZeroAmbientMap phi (j i z)) (sphere (0 : V2) 1)) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap phi ∧
      (∀ i, ∀ z : Disk, hamiltonZeroAmbientMap psi (j i z) = q i z) ∧
      (R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) ∧
      (R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.1 = hamiltonZeroThirdCircleMap phi x) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b) ∨
      ∃ i, HamiltonZeroDiskFailureArc e R phi (j i) (theta i) alpha beta a b := by
  classical
  by_cases hinj : ∀ i, InjOn (fun z => hamiltonZeroAmbientMap phi (j i z)) (sphere (0 : V2) 1)
  · exact Or.inl (exists_hamiltonZero_homeomorphic_disk_family_installation
      hd hphi F heR j hj hji hjR hrim hdis halpha hab hbeta ha horder hb
      hfirst hsecond theta hthird hboundaryEdges hinj)
  · right
    push Not at hinj
    obtain ⟨i, hi⟩ := hinj
    exact ⟨i, exists_hamiltonZero_disk_failure_arc_of_not_injective_rim
      phi heR.closed (j i) (hj i) (hji i) (hjR i) (hrim i)
      halpha hbeta ha hb hfirst hsecond (theta i) (hthird i) hi⟩

end PoincareConjecture.M76
