import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.OriginalNonsphericalIncompressibleSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.NonsphericalFrontierGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.ClopenIncompressibility

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

theorem exists_hamiltonZero_nontrivial_incompressible_frontier {ι κ : Type*}
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
        ∃ (Nlower Nupper : Set X0)
          (lower : FrontierResidualModel e Nlower (q ⁻¹' {(a : C0)}))
          (upper : FrontierResidualModel e Nupper (q ⁻¹' {(b : C0)})),
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (lower.components i))) ∧
          (∀ i, ¬ Nonempty (ChartwisePLSphere e (upper.components i))) ∧
          (∀ i (x : lower.components i), Nontrivial (FundamentalGroup (lower.components i) x)) ∧
          (∀ i (x : upper.components i), Nontrivial (FundamentalGroup (upper.components i) x)) ∧
          ∀ T ∈ ({R, (interior R)ᶜ} : Set (Set X0)),
            ∃ hFT : frontier R ⊆ T,
              ∀ x : frontier R,
                Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hFT) x) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  obtain ⟨a, ha, b, hb, psi, hpsi, H, Fpsi, he, hfront,
    Nlower, Nupper, lower, upper, hnosphereA, hnosphereB, hinj⟩ :=
    exists_hamiltonZero_nonspherical_incompressible_slab e d hI hd phi hphi F
  let q := hamiltonZeroCircleMap psi
  let A := q ⁻¹' {(a : C0)}
  let B := q ⁻¹' {(b : C0)}
  let R := q ⁻¹' AddCircle.closedIntervalArc p a b
  have hA : IsClosed A := isClosed_singleton.preimage q.continuous
  have hB : IsClosed B := isClosed_singleton.preimage q.continuous
  have hab : (a : C0) ≠ (b : C0) := by
    intro h
    have haP : a ∈ Ico (0 : ℝ) (0 + p) := ⟨by linarith [ha.1], by linarith [ha.2]⟩
    have hbP : b ∈ Ico (0 : ℝ) (0 + p) := ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico haP hbP).mp h
    linarith [ha.2, hb.1]
  have hAB : Disjoint A B := Set.disjoint_left.mpr (fun x hx hy => hab (hx.symm.trans hy))
  have hsplit : frontier R = A ∪ B := by
    rw [hfront]
    ext x
    simp [A, B, q]
  have hRne : R.Nonempty := by
    obtain ⟨x, hx⟩ := (lower.component ⟨0, lower.positive⟩).2.1.nonempty
    exact ⟨x, he.closed.frontier_subset (hsplit.symm ▸
      Or.inl ((lower.component ⟨0, lower.positive⟩).2.2.1 hx))⟩
  have hgroupsA (i) (x : lower.components i) :
      Nontrivial (FundamentalGroup (lower.components i) x) := by
    have hsplit' : frontier R = B ∪ A := hsplit.trans (union_comm A B)
    exact (he.nonspherical_frontier_component_groups he.closed.isCompact hRne
      hB hA hAB.symm hsplit' (lower.component i).2.1
      (lower.component i).2.2.1 (lower.component i).2.2.2 (hnosphereA i)).2.1 x
  have hgroupsB (i) (x : upper.components i) :
      Nontrivial (FundamentalGroup (upper.components i) x) :=
    (he.nonspherical_frontier_component_groups he.closed.isCompact hRne
      hA hB hAB hsplit (upper.component i).2.1
      (upper.component i).2.2.1 (upper.component i).2.2.2 (hnosphereB i)).2.1 x
  refine ⟨a, ha, b, hb, psi, hpsi, H, Fpsi, he, hfront,
    Nlower, Nupper, lower, upper, hnosphereA, hnosphereB, hgroupsA, hgroupsB, ?_⟩
  intro T hT
  obtain ⟨hAT, hiA⟩ := hinj T hT (a : C0) (by simp)
  obtain ⟨hBT, hiB⟩ := hinj T hT (b : C0) (by simp)
  have hFT : frontier R ⊆ T := by
    rw [hsplit]
    exact union_subset hAT hBT
  refine ⟨hFT, ?_⟩
  intro x
  exact FundamentalGroup.inclusion_injective_of_disjoint_closed_union
    hA hB hAB hsplit hFT (fun _ y => hiA y) (fun _ y => hiB y) x

end PoincareConjecture.M76
