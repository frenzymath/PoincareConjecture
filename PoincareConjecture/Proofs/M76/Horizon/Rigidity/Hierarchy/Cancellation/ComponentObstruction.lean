import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.CollaredRegion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.RestrictedPhaseCollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.ComplementarySlabDomains









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

theorem hamiltonZero_component_frontier_not_subset_single_phase
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
    (hmin : ∀ m, HamiltonZeroIncompressiblePhaseCount e d base m →
      lower.count + upper.count ≤ m)
    (complementary side : Bool)
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {K : Set E} (hK : IsCompact K) (c : E × ℝ → X0)
    {r : ℝ} (hr : 0 < r)
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hopen : IsOpen (c '' (K ×ˢ Ioo (-r) r))) :
    let l := if complementary then b else a
    let u := if complementary then a + p else b
    let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p l u
    let S := hamiltonZeroCircleMap phi ⁻¹' {((if side then u else l : ℝ) : C0)}
    c '' (K ×ˢ ({0} : Set ℝ)) = S →
    (∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2) →
    (∀ z ∈ K ×ˢ Icc (-r) 0, hamiltonZeroCircleMap phi (c z) =
      ((if side then u - z.2 else l + z.2 : ℝ) : C0)) →
    ∀ x ∈ R, ¬ frontier (connectedComponentIn R x) ⊆ S := by
  intro l u R S hzero hside hphase x hx hsingle
  let : Fact (0 < p) := ⟨by norm_num⟩
  let Q := hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
  let : T2Space X0 := Q.isEmbedding.t2Space
  let : CompactSpace X0 := Q.symm.compactSpace
  let : PreconnectedSpace X0 := preconnectedSpace_iff_univ.mpr (by
    simpa only [image_univ, Q.symm.surjective.range_eq] using
      isPreconnected_univ.image Q.symm Q.symm.continuous.continuousOn)
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbp : b < p := by linarith [hb.2]
  have hcomp := circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap phi)
    ha0 hab hbp hfront
  have heR : PLDomain e R := by
    cases complementary
    · exact he
    · simpa only [R, l, u, ↓reduceIte, hcomp] using he.compl_interior.1
  have hRfront : frontier R = hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)} := by
    cases complementary
    · exact hfront
    · simpa only [R, l, u, ↓reduceIte, hcomp] using he.compl_interior.2.trans hfront
  have hSF : S ⊆ frontier R := by
    rw [hRfront]
    intro y hy
    change hamiltonZeroCircleMap phi y = _ at hy
    cases complementary <;> cases side <;>
      simp only [l, u, Bool.false_eq_true, ↓reduceIte, AddCircle.coe_add_period] at hy <;>
      simp [hy]
  let P := connectedComponentIn R x
  have hPsub : P ⊆ R := connectedComponentIn_subset R x
  have hPne : P.Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hPproper : P ≠ univ := by
    intro hPu
    have hall : ∀ y, y ∈ R := fun y => hPsub (hPu.symm ▸ mem_univ y)
    cases complementary
    · obtain ⟨y, hy⟩ := surjective_hamiltonZeroCircleMap phi F (0 : C0)
      have hmem := hall y
      change hamiltonZeroCircleMap phi y ∈ AddCircle.closedIntervalArc p a b at hmem
      rw [hy] at hmem
      exact AddCircle.zero_notMem_closedIntervalArc p ha0 hbp hmem
    · obtain ⟨y, hy⟩ := surjective_hamiltonZeroCircleMap phi F (((a + b) / 2 : ℝ) : C0)
      have hmem := hall y
      change hamiltonZeroCircleMap phi y ∈ AddCircle.closedIntervalArc p b (a + p) at hmem
      rw [hy, ← AddCircle.compl_interior_closedIntervalArc p ha0 hab hbp] at hmem
      apply hmem
      rw [AddCircle.interior_closedIntervalArc p ha0 hbp]
      exact ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hPfront : (frontier P).Nonempty := nonempty_frontier_iff.mpr ⟨hPne, hPproper⟩
  obtain ⟨hPc, heP, hKc, _, hic, hopenc, _, hsidec, hnec, hfull⟩ :=
    heR.restrict_phase_collar_to_component heR.closed.isCompact hx hSF hK c hr hi
      hzero hside hopen
  have hKne : ({z | z ∈ K ∧ c (z, 0) ∈ P} : Set E).Nonempty :=
    hnec.mpr (hPfront.mono fun y hy => ⟨hsingle hy, hPc.isClosed.frontier_subset hy⟩)
  have hphasec : ∀ z ∈ {z | z ∈ K ∧ c (z, 0) ∈ P} ×ˢ Icc (-r) 0,
      hamiltonZeroCircleMap phi (c z) =
        ((if side then u - z.2 else l + z.2 : ℝ) : C0) :=
    fun z hz => hphase z ⟨hz.1.1, hz.2⟩
  have hdecrease : ∃ m, HamiltonZeroIncompressiblePhaseCount e d base m ∧
      m < lower.count + upper.count := by
    cases complementary
    · exact exists_hamiltonZero_smaller_phase_count_of_collared_region hI hd hphi Hbase F
        ha hb he hfront hinj lower upper hnoA hnoB hgroupsA hgroupsB hPc hPsub
        hKc hKne c hr side hic (hfull hsingle) hsidec hopenc hphasec
    · exact exists_hamiltonZero_smaller_phase_count_of_complementary_collared_region
        hI hd hphi Hbase F ha hb he hfront hinj lower upper hnoA hnoB hgroupsA hgroupsB
        hPc hPsub hKc hKne c hr side hic (hfull hsingle) hsidec hopenc hphasec
  obtain ⟨m, hm, hlt⟩ := hdecrease
  exact (Nat.not_lt_of_ge (hmin m hm)) hlt

end PoincareConjecture.M76
