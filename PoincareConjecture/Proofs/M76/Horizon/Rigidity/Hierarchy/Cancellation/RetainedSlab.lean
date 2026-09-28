import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.ClosedPhaseRegion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.FrontierInjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.MinimalFirstPhaseComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.ResidualComponentDeletion










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

theorem exists_hamiltonZero_smaller_phase_count_of_closed_region
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {base phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (Hbase : base.HomotopyRel phi B0)
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {a b : ℝ} (ha : a ∈ Ioo (p / 4) (p / 3))
    (hb : b ∈ Ioo (2 * p / 3) (3 * p / 4))
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)})
    (hinj : ∀ x : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b),
      Function.Injective (FundamentalGroup.map (VanKampen.inclusion _) x))
    {Nlower Nupper : Set X0}
    (lower : FrontierResidualModel e Nlower (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}))
    (upper : FrontierResidualModel e Nupper (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}))
    (hnoA : ∀ i, ¬ Nonempty (ChartwisePLSphere e (lower.components i)))
    (hnoB : ∀ i, ¬ Nonempty (ChartwisePLSphere e (upper.components i)))
    (hgroupsA : ∀ i (x : lower.components i), Nontrivial (FundamentalGroup (lower.components i) x))
    (hgroupsB : ∀ i (x : upper.components i), Nontrivial (FundamentalGroup (upper.components i) x))
    {D : Set X0} (hD : IsClosed D)
    {cut u v lambda : ℝ} (hu : cut < u) (hv : v < cut + p)
    (hlambda : lambda ∈ Icc u v)
    (haLambda : (a : C0) ≠ (lambda : C0)) (hbLambda : (b : C0) ≠ (lambda : C0))
    (hrange : D ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v)
    (hDfront : ∀ x ∈ frontier D, hamiltonZeroCircleMap phi x = (lambda : C0))
    (hmeet : ((hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)}) ∩ D).Nonempty) :
    ∃ m, HamiltonZeroIncompressiblePhaseCount e d base m ∧ m < lower.count + upper.count := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨psi, hpsi, ⟨Hpsi⟩, ⟨Fpsi⟩, _, hlevel, hdomain, _⟩ :=
    exists_hamiltonZero_closed_phase_region_cancellation hd hphi F hD hu hv
      hlambda hrange hDfront
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hb64 : b < p := by linarith [hb.2]
  have hAfront := AddCircle.frontier_closedIntervalArc p ha0 hab.le hb64
  obtain ⟨heNew, hfNew⟩ := hdomain (AddCircle.closedIntervalArc p a b)
    (AddCircle.isCompact_closedIntervalArc p a b).isClosed (by
      rw [hAfront]
      exact fun h => h.elim (fun h => haLambda h.symm) (fun h => hbLambda h.symm))
    he (hfront.trans (congrArg (fun S => hamiltonZeroCircleMap phi ⁻¹' S) hAfront.symm))
  rw [hAfront] at hfNew
  have havoid (c : C0) (hc : c ≠ (lambda : C0)) :
      Disjoint (hamiltonZeroCircleMap phi ⁻¹' {c}) (frontier D) := by
    apply disjoint_left.mpr
    intro x hx hxD
    exact hc (hx.symm.trans (hDfront x hxD))
  have hnonempty (c : C0) (hc : c ≠ (lambda : C0)) :
      ((hamiltonZeroCircleMap phi ⁻¹' {c}) \ D).Nonempty := by
    rw [← hlevel c hc]
    obtain ⟨x, hx⟩ := surjective_hamiltonZeroCircleMap psi Fpsi c
    exact ⟨x, hx⟩
  have hlow := lower.exists_retained_model_after_closed_excision hD
    (havoid _ haLambda) (hnonempty _ haLambda)
  have hup := upper.exists_retained_model_after_closed_excision hD
    (havoid _ hbLambda) (hnonempty _ hbLambda)
  rw [← hlevel _ haLambda] at hlow
  rw [← hlevel _ hbLambda] at hup
  obtain ⟨lowerNew, hleA, hltA, fA, hfA⟩ := hlow
  obtain ⟨upperNew, hleB, hltB, fB, hfB⟩ := hup
  have hnoANew (i) : ¬ Nonempty (ChartwisePLSphere e (lowerNew.components i)) := by
    rw [hfA i]
    exact hnoA (fA i)
  have hnoBNew (i) : ¬ Nonempty (ChartwisePLSphere e (upperNew.components i)) := by
    rw [hfB i]
    exact hnoB (fB i)
  have hgANew (i) : ∀ x : lowerNew.components i,
      Nontrivial (FundamentalGroup (lowerNew.components i) x) := by
    rw [hfA i]
    exact hgroupsA (fA i)
  have hgBNew (i) : ∀ x : upperNew.components i,
      Nontrivial (FundamentalGroup (upperNew.components i) x) := by
    rw [hfB i]
    exact hgroupsB (fB i)
  have hdeleted : frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) \ D := by
    rw [hfNew, hfront]
    ext x
    have hA := Set.ext_iff.mp (hlevel _ haLambda) x
    have hB := Set.ext_iff.mp (hlevel _ hbLambda) x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, mem_sdiff] at *
    tauto
  have hcount : lowerNew.count + upperNew.count < lower.count + upper.count := by
    obtain ⟨x, hx, hxD⟩ := hmeet
    rcases hx with hxa | hxb
    · have := hltA ⟨x, hxa, hxD⟩
      omega
    · have := hltB ⟨x, hxb, hxD⟩
      omega
  have hinjNew := frontier_ambient_injective_of_closed_deletion hD hdeleted hinj
  obtain ⟨hA, _, hB, _, hAB, hR, _, _, hminus, heminus, _, hne, hneminus⟩ :=
    PrescribedSlab.exists_hamiltonZero_circle_slab
      e d hd psi hpsi Fpsi a b ha0 hab hb64 heNew hfNew
  have hside := heNew.closed_sides_ambient_injective_of_frontier_ambient
    hR hminus hne hneminus hinjNew
  let Rnew := hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b
  have hsplit : frontier Rnew =
      (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}) ∪
        (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}) := by
    rw [hfNew]
    ext x
    simp
  have hRall : Rnew ⊆ latticeHandleDomain (Fin 0) (Fin 3) L0 := by
    rw [hamiltonZeroDomain_eq_univ]
    exact subset_univ _
  have hTall : (interior Rnew)ᶜ ⊆ latticeHandleDomain (Fin 0) (Fin 3) L0 := by
    rw [hamiltonZeroDomain_eq_univ]
    exact subset_univ _
  have hirrR := hI.of_frontier_component_models heNew hRall hA.isClosed hB.isClosed
    hAB hsplit lowerNew upperNew hgANew hgBNew hinjNew
  have hfrontT : frontier (interior Rnew)ᶜ = frontier Rnew := heNew.frontier_closed_exterior
  have hinjT : ∀ x : frontier (interior Rnew)ᶜ, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion (frontier (interior Rnew)ᶜ)) x) := by
    rw [hfrontT]
    exact hinjNew
  have hirrT := hI.of_frontier_component_models heminus hTall hA.isClosed hB.isClosed
    hAB (hfrontT.trans hsplit) lowerNew upperNew hgANew hgBNew hinjT
  refine ⟨lowerNew.count + upperNew.count, ?_, hcount⟩
  exact ⟨a, ha, b, hb, psi, hpsi, ⟨Hbase.trans Hpsi⟩, ⟨Fpsi⟩,
    heNew, hfNew, hirrR, hirrT, hinjNew, hside, Nlower, Nupper,
    lowerNew, upperNew, rfl, hnoANew, hnoBNew, hgANew, hgBNew⟩

end PoincareConjecture.M76
