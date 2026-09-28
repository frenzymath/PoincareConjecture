import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskFamilyInstallation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.DiskBoundaryExtension

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
local notation "Rim" => (Set.ofPred (fun z : Disk => (z : V2) ∈ sphere (0 : V2) 1))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_homeomorphic_disk_family_installation
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
    (hinj : ∀ i, InjOn (fun z => hamiltonZeroAmbientMap phi (j i z)) (sphere (0 : V2) 1)) :
    ∃ (v w : η → V2 → ℝ) (q : η → V2 → X0)
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
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b := by
  classical
  have hex (i : η) := exists_hamiltonZero_source_disk_homeomorphic_normal_form
    hd hphi (j i) (hj i) halpha hab hbeta ha horder hb
      (fun z hz => hfirst (hjR i hz)) (fun z hz => hsecond (hjR i hz))
      (theta i) (fun z hz => hthird i ⟨z, hz⟩) (hboundaryEdges i) (hinj i)
  choose v w q E hv hw hE hEval hq hcoords hqi hboundary qD hqD H hH using hex
  have hrange (i : η) (z : V2) (hz : z ∈ Disk) :
      v i z ∈ Icc alpha beta ∧ w i z ∈ Icc a b := by
    have h := (E i ⟨z, hz⟩).property
    rwa [hEval] at h
  have hphase (i : η) (z : Disk) : (Q0 (qD i z)).1.1 =
      (Q0 (hamiltonZeroAmbientMap phi (j i z))).1.1 := by
    rw [hqD, hcoords i z z.property]
    exact (hthird i z).symm
  have hfirstD (i : η) (z : Disk) : (Q0 (qD i z)).2 ∈ AddCircle.closedIntervalArc p alpha beta := by
    rw [hqD, hcoords i z z.property]
    exact ⟨v i z, (hrange i z z.property).1, rfl⟩
  have hsecondD (i : η) (z : Disk) : (Q0 (qD i z)).1.2 ∈ AddCircle.closedIntervalArc p a b := by
    rw [hqD, hcoords i z z.property]
    exact ⟨w i z, (hrange i z z.property).2, rfl⟩
  obtain ⟨psi, hpsi, Hpsi, Fpsi, hsame, hbase, hRfirst, hRsecond, G, hGphase, hGarc⟩ :=
    exists_hamiltonZero_finite_marked_disk_installation hd hphi F heR
      j hj hji hjR hrim hdis q hq qD (fun i z => (hqD i z).symm) hphase H
      halpha hab.le hbeta ha horder.le hb hsecond hsecondD hfirst hfirstD
  exact ⟨v, w, q, E, psi, hv, hw, hE, hEval, hrange, hq, hcoords, hqi, hboundary, hpsi, Hpsi, Fpsi,
    hsame, fun i z => (hbase i z).trans (hqD i z), hRfirst, hRsecond, G, hGphase, hGarc⟩

end PoincareConjecture.M76
