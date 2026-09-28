import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.OriginalIrreducibleSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.ResidualModelInvariance










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p


theorem FrontierResidualModel.count_eq_of_same_surface
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N N' F : Set X}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel e N' F) :
    M.count = M'.count := by
  obtain ⟨r, _⟩ := M.exists_component_matching M'
  simpa only [Fintype.card_fin] using Fintype.card_congr r



def HamiltonZeroIncompressiblePhaseCount {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (n : ℕ) : Prop :=
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ psi : C(H0, H0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        let q := hamiltonZeroCircleMap psi
        let R := q ⁻¹' AddCircle.closedIntervalArc p a b
        PLDomain e R ∧ frontier R = q ⁻¹' {(a : C0), (b : C0)} ∧
        IsPLIrreducible e R ∧ IsPLIrreducible e (interior R)ᶜ ∧
        (∀ x : frontier R, Function.Injective
          (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x)) ∧
        (∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X0)), ∀ x : T,
          Function.Injective (FundamentalGroup.map (VanKampen.inclusion T) x)) ∧
        ∃ (Nlower Nupper : Set X0)
          (lower : FrontierResidualModel e Nlower (q ⁻¹' {(a : C0)}))
          (upper : FrontierResidualModel e Nupper (q ⁻¹' {(b : C0)})),
          lower.count + upper.count = n ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (lower.components i))) ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (upper.components i))) ∧
          (∀ i (x : lower.components i), Nontrivial (FundamentalGroup (lower.components i) x)) ∧
          (∀ i (x : upper.components i), Nontrivial (FundamentalGroup (upper.components i) x))

theorem exists_hamiltonZero_minimal_incompressible_phase_count {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
    ∃ n, HamiltonZeroIncompressiblePhaseCount e d phi n ∧
      ∀ m, HamiltonZeroIncompressiblePhaseCount e d phi m → n ≤ m := by
  classical
  have hex : ∃ n, HamiltonZeroIncompressiblePhaseCount e d phi n := by
    obtain ⟨a, ha, b, hb, psi, hpsi, H, Fpsi, he, hfront, hIR, hIT,
        hfrontPi, hsidePi, Nlower, Nupper, lower, upper, hnosphereA, hnosphereB,
        hgroupsA, hgroupsB⟩ :=
      exists_hamiltonZero_irreducible_incompressible_slab e d hI hd phi hphi F
    exact ⟨lower.count + upper.count, a, ha, b, hb, psi, hpsi, H, Fpsi,
      he, hfront, hIR, hIT, hfrontPi, hsidePi, Nlower, Nupper, lower, upper, rfl,
      hnosphereA, hnosphereB, hgroupsA, hgroupsB⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hm => Nat.find_min' hex hm⟩

end PoincareConjecture.M76

