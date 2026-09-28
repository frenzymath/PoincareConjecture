import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.OriginalIrreducibleSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalPhaseMapGroups

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

theorem hamiltonZero_phase_injections_of_frontier
    (psi : C(H0, H0)) (Fpsi : (ContinuousMap.id H0).HomotopyRel psi B0)
    {R : Set X0} {a b : ℝ}
    (ha : a ∈ Ioo (p / 4) (p / 3)) (hb : b ∈ Ioo (2 * p / 3) (3 * p / 4))
    (hfront : frontier R = hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)})
    (hfrontAmbient : ∀ x : frontier R, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x)) :
    ∀ theta ∈ ({(a : C0), (b : C0)} : Set C0),
      ∀ x : hamiltonZeroCircleMap psi ⁻¹' {theta},
        Function.Injective (FundamentalGroup.map
          (VanKampen.inclusion (hamiltonZeroCircleMap psi ⁻¹' {theta})) x) ∧
        Function.Injective (FundamentalGroup.map (hamiltonZeroPhaseMap psi theta) x) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let q := hamiltonZeroCircleMap psi
  let A := q ⁻¹' {(a : C0)}
  let B := q ⁻¹' {(b : C0)}
  have hA : IsClosed A := isClosed_singleton.preimage q.continuous
  have hB : IsClosed B := isClosed_singleton.preimage q.continuous
  have hab : (a : C0) ≠ (b : C0) := by
    intro h
    have haP : a ∈ Ico (0 : ℝ) (0 + p) := ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have hbP : b ∈ Ico (0 : ℝ) (0 + p) := ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico haP hbP).mp h
    linarith [ha.2, hb.1]
  have hAB : Disjoint A B := Set.disjoint_left.mpr (fun _ hx hy => hab (hx.symm.trans hy))
  have hsplit : frontier R = A ∪ B := by
    rw [hfront]
    ext x
    simp [A, B, q]
  have phaseInjection {S T : Set X0} (hS : IsClosed S) (hT : IsClosed T)
      (hST : Disjoint S T) (hsplit : frontier R = S ∪ T) (x : S) :
      Function.Injective (FundamentalGroup.map (VanKampen.inclusion S) x) := by
    have hSF : S ⊆ frontier R := hsplit.symm ▸ subset_union_left
    have hinj := FundamentalGroup.inclusion_injective_of_closed_partition
      hS hT hST hsplit hSF x
    have hfactor : VanKampen.inclusion S =
        (VanKampen.inclusion (frontier R)).comp (ContinuousMap.inclusion hSF) := rfl
    rw [hfactor, FundamentalGroup.map_comp]
    exact (hfrontAmbient (ContinuousMap.inclusion hSF x)).comp hinj
  intro theta htheta x
  have hi : Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (q ⁻¹' {theta})) x) := by
    rcases htheta with rfl | rfl
    · exact phaseInjection hA hB hAB hsplit x
    · exact phaseInjection hB hA hAB.symm (hsplit.trans (union_comm A B)) x
  exact ⟨hi, hamiltonZeroPhaseMap_pi1_injective psi Fpsi theta x hi⟩

theorem exists_hamiltonZero_injective_phase_maps {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0) :
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
        (∀ theta ∈ ({(a : C0), (b : C0)} : Set C0),
          ∀ x : q ⁻¹' {theta},
            Function.Injective (FundamentalGroup.map
              (VanKampen.inclusion (q ⁻¹' {theta})) x) ∧
            Function.Injective (FundamentalGroup.map (hamiltonZeroPhaseMap psi theta) x)) ∧
        ∃ (Nlower Nupper : Set X0)
          (lower : FrontierResidualModel e Nlower (q ⁻¹' {(a : C0)}))
          (upper : FrontierResidualModel e Nupper (q ⁻¹' {(b : C0)})),
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (lower.components i))) ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (upper.components i))) ∧
          (∀ i (x : lower.components i), Nontrivial (FundamentalGroup (lower.components i) x)) ∧
          (∀ i (x : upper.components i), Nontrivial (FundamentalGroup (upper.components i) x)) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  obtain ⟨a, ha, b, hb, psi, hpsi, H, ⟨Fpsi⟩, he, hfront, hirrR, hirrS,
    hfrontAmbient, hsides, Nlower, Nupper, lower, upper,
    hnosphereA, hnosphereB, hgroupsA, hgroupsB⟩ :=
    exists_hamiltonZero_irreducible_incompressible_slab e d hI hd phi hphi F
  exact ⟨a, ha, b, hb, psi, hpsi, H, ⟨Fpsi⟩, he, hfront,
    hirrR, hirrS, hfrontAmbient, hsides,
    hamiltonZero_phase_injections_of_frontier psi Fpsi ha hb hfront hfrontAmbient,
    Nlower, Nupper, lower, upper, hnosphereA, hnosphereB, hgroupsA, hgroupsB⟩

end PoincareConjecture.M76
