import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.OriginalNontrivialFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.CollarGluing.OriginalDomainInjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.CutIrreducibility
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.Compression.Slab

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

theorem exists_hamiltonZero_irreducible_incompressible_slab {ι κ : Type*}
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
        ∃ (Nlower Nupper : Set X0)
          (lower : FrontierResidualModel e Nlower (q ⁻¹' {(a : C0)}))
          (upper : FrontierResidualModel e Nupper (q ⁻¹' {(b : C0)})),
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (lower.components i))) ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (upper.components i))) ∧
          (∀ i (x : lower.components i), Nontrivial (FundamentalGroup (lower.components i) x)) ∧
          (∀ i (x : upper.components i), Nontrivial (FundamentalGroup (upper.components i) x)) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨a, ha, b, hb, psi, hpsi, H, ⟨Fpsi⟩, he, hfront,
    Nlower, Nupper, lower, upper, hnosphereA, hnosphereB, hgroupsA, hgroupsB, hpi⟩ :=
    exists_hamiltonZero_nontrivial_incompressible_frontier e d hI hd phi hphi F
  let q := hamiltonZeroCircleMap psi
  let A := q ⁻¹' {(a : C0)}
  let B := q ⁻¹' {(b : C0)}
  let R := q ⁻¹' AddCircle.closedIntervalArc p a b
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hb64 : b < p := by linarith [hb.2]
  obtain ⟨hA, _, hB, _, hAB, hR, _, _, hminus, heminus, hfrontminus, hne, hneminus⟩ :=
    PrescribedSlab.exists_hamiltonZero_circle_slab
      e d hd psi hpsi Fpsi a b ha0 hab hb64 he hfront
  have hside := he.closed_sides_ambient_injective hR hminus hne hneminus hpi
  obtain ⟨hFR, hFRi⟩ := hpi R (Or.inl rfl)
  have hfrontAmbient (x : frontier R) : Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier R)) x) := by
    have heq : VanKampen.inclusion (frontier R) =
        (VanKampen.inclusion R).comp (ContinuousMap.inclusion hFR) := rfl
    rw [heq, FundamentalGroup.map_comp]
    exact (hside R (Or.inl rfl) (ContinuousMap.inclusion hFR x)).comp (hFRi x)
  have hsplit : frontier R = A ∪ B := by
    rw [hfront]
    ext x
    simp [A, B, q]
  have hRall : R ⊆ latticeHandleDomain (Fin 0) (Fin 3) L0 := by
    rw [hamiltonZeroDomain_eq_univ]
    exact subset_univ _
  have hTall : (interior R)ᶜ ⊆ latticeHandleDomain (Fin 0) (Fin 3) L0 := by
    rw [hamiltonZeroDomain_eq_univ]
    exact subset_univ _
  have hirrR := hI.of_frontier_component_models he hRall hA.isClosed hB.isClosed
    hAB hsplit lower upper hgroupsA hgroupsB hfrontAmbient
  have hfrontT : frontier (interior R)ᶜ = frontier R := he.frontier_closed_exterior
  have hfrontAmbientT : ∀ x : frontier (interior R)ᶜ, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier (interior R)ᶜ)) x) := by
    rw [hfrontT]
    exact hfrontAmbient
  have hirrT := hI.of_frontier_component_models heminus hTall hA.isClosed hB.isClosed
    hAB (hfrontT.trans hsplit) lower upper hgroupsA hgroupsB hfrontAmbientT
  exact ⟨a, ha, b, hb, psi, hpsi, H, ⟨Fpsi⟩, he, hfront,
    hirrR, hirrT, hfrontAmbient, hside, Nlower, Nupper, lower, upper,
    hnosphereA, hnosphereB, hgroupsA, hgroupsB⟩

end PoincareConjecture.M76
