import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.SourceIncompressiblePhases
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Spheres.MinimalRemoval
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.IrreducibleSlabs

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1

theorem exists_hamiltonZero_boundary_meeting_third_hierarchy
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (hI : IsPLIrreducible e R)
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    {cut alpha beta cut' u v : ℝ}
    (halpha : cut < alpha) (hbeta : beta < cut + p)
    (hu : cut' < u) (hv : v < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v)
    (j : ℝ × ℝ → X0) (hj : j '' Ann ⊆ frontier R)
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c)
    (delta0 delta1 : ℝ) (theta : C0)
    (hvalue : ∀ z : Ann, hamiltonZeroAmbientMap phi (j z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (∀ t ∈ ({a, b} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e R phi (t : C0)) ∧
      ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
        (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
        hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
        hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
        HamiltonZeroThirdPhaseGeometry e R psi a b ∧
        (∀ xi : C0, (frontier R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {xi}).Nonempty) ∧
        (∀ t ∈ ({a, b} : Set ℝ), ∀ S : Set X0, S.Nonempty →
          S ⊆ R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)} →
          (∀ x ∈ S, connectedComponentIn
            (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)}) x = S) →
          (S ∩ frontier R).Nonempty) ∧
        ∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) := by
  obtain ⟨a, ha, b, hb, hreg, eta, A, hA, hAR, hfixedEta, hfirstEta, hsecondEta,
      heta, ⟨Heta⟩, ⟨Feta⟩, ⟨HextEta⟩, hcuts, hinj, hboundary⟩ :=
    exists_hamiltonZero_incompressible_third_hierarchy e d hd phi hphi F0 hI.1
      j hj c hc delta0 delta1 theta hvalue
  have geometry : HamiltonZeroThirdPhaseGeometry e R eta a b := by
    refine ⟨hcuts, ?_⟩
    intro t ht x
    let incl := ContinuousMap.inclusion
      (inter_subset_left : R ∩ hamiltonZeroThirdCircleMap eta ⁻¹' {(t : C0)} ⊆ R)
    let ambient : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
    change Function.Injective (FundamentalGroup.map (ambient.comp incl) x)
    rw [FundamentalGroup.map_comp]
    exact (hinjR (incl x)).comp ((hinj t ht).2 x)
  have hfirstEtaR : R ⊆ hamiltonZeroCircleMap eta ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [hfirstEta]
    exact hfirst
  have hsecondEtaR : R ⊆ hamiltonZeroSecondCircleMap eta ⁻¹' AddCircle.closedIntervalArc p u v := by
    rw [hsecondEta]
    exact hsecond
  obtain ⟨psi, B, hB, hBR, hfixedPsi, hfirstPsi, hsecondPsi, hpsi, ⟨Hpsi⟩, Fpsi,
      ⟨HextPsi⟩, geom, hcomponents⟩ :=
    exists_hamiltonZero_third_phases_without_closed_components e d hd phi eta heta Feta
      hI hA hAR hfixedEta (by linarith [ha.1]) (by linarith [ha.2, hb.1])
      (by linarith [hb.2]) hreg geometry halpha hbeta hu hv hfirstEtaR hsecondEtaR
  have hsupport : A ∪ B ⊆ interior R := union_subset hAR hBR
  have hfixed (x : X0) (hx : x ∉ A ∪ B) :
      hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x :=
    (hfixedPsi x (fun h => hx (Or.inr h))).trans
      (hfixedEta x (fun h => hx (Or.inl h)))
  refine ⟨a, ha, b, hb, hreg, psi, A ∪ B, hA.union hB, hsupport, hfixed,
    hfirstPsi.trans hfirstEta, hsecondPsi.trans hsecondEta, hpsi,
    ⟨Heta.trans Hpsi⟩, Fpsi, ⟨HextEta.trans HextPsi⟩, geom, ?_, hcomponents, ?_⟩
  · intro xi
    obtain ⟨x, hxfront, hxphase⟩ := hboundary xi
    refine ⟨x, hxfront, ?_⟩
    change hamiltonZeroThirdCircleMap psi x = xi
    rw [hamiltonZeroThirdCircleMap_ambient,
      hfixedPsi x (fun h => hxfront.2 (hBR h)), ← hamiltonZeroThirdCircleMap_ambient]
    exact hxphase
  · apply isPLIrreducible_hamiltonZero_complementary_third_slabs psi hI
      (fun side => ⟨(geom.slabs side).1, (geom.slabs side).2.1⟩)
    intro t ht x hx
    exact hcomponents t ht
      (connectedComponentIn (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)}) x)
      ⟨x, mem_connectedComponentIn hx⟩ (connectedComponentIn_subset _ _)
      (fun y hy => (connectedComponentIn_eq hy).symm)

end PoincareConjecture.M76
