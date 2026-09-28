import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.BoundaryNonempty
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ComplementaryThirdSlabs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Compression.ComplementaryIncompressiblePhases










set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1

theorem exists_hamiltonZero_incompressible_third_hierarchy
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
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
        (∀ side : Bool,
          let N := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
            ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(a : C0)}) ∪
              (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(b : C0)})) ∧
          ∀ t ∈ ({a, b} : Set ℝ),
            ∃ hSN : R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)} ⊆ N,
              ∀ x, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x)) ∧
        (∀ t ∈ ({a, b} : Set ℝ),
          let S := R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(t : C0)}
          S.Nonempty ∧ ∀ x : S,
            Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x)) ∧
        ∀ xi : C0, (frontier R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {xi}).Nonempty := by
  have hboundary := hamiltonZero_installed_annulus_third_boundary_levels_nonempty
    phi j hj c hc delta0 delta1 theta hvalue
  obtain ⟨a, ha, b, hb, hreg, hslabs⟩ :=
    exists_hamiltonZero_complementary_third_slabs e d hd phi hphi heR
  obtain ⟨he, hf⟩ := hslabs (a, b) (Or.inl rfl)
  obtain ⟨psi, A, hA, hAR, hfixed, hfirst, hsecond, hpsi, Hpsi, Fpsi, Hext, hcuts, hinj⟩ :=
    exists_hamiltonZero_complementary_third_phases_injective e d hd phi hphi F0 heR
      (by linarith [ha.1]) (by linarith [ha.2, hb.1]) (by linarith [hb.2])
      he (hslabs (b, a + p) (Or.inr rfl)).1 hf hreg (fun t _ => hboundary t)
  refine ⟨a, ha, b, hb, hreg, psi, A, hA, hAR, hfixed, hfirst, hsecond,
    hpsi, Hpsi, Fpsi, Hext, hcuts, hinj, ?_⟩
  intro xi
  obtain ⟨x, hx, hqx⟩ := hboundary xi
  refine ⟨x, hx, ?_⟩
  change hamiltonZeroThirdCircleMap psi x = xi
  rw [hamiltonZeroThirdCircleMap_ambient, hfixed x (fun h => hx.2 (hAR h))]
  exact hqx

end PoincareConjecture.M76
