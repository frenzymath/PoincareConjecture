import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.ComponentObstruction










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem PLDomain.frontier_connectedComponentIn_of_compact
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) {x : X} (hx : x ∈ R) :
    frontier (_root_.connectedComponentIn R x) =
      _root_.connectedComponentIn R x ∩ frontier R := by
  let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
  have hclosed := (Set.isCompact_connectedComponentIn_of_mem hR hx).isClosed
  obtain ⟨U, hU, hPU⟩ := Set.exists_open_inter_of_relative_open
    (connectedComponentIn_subset R x) (Set.isOpen_preimage_connectedComponentIn hx)
  exact Set.frontier_eq_inter_of_eq_inter_open he.closed hclosed hU hPU

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem hamiltonZero_component_has_other_boundary_phase
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
    ∀ x ∈ R, ∃ y ∈ frontier (connectedComponentIn R x),
      hamiltonZeroCircleMap phi y = ((if side then l else u : ℝ) : C0) ∧
      ∀ z ∈ frontier R, z ∈ S → y ∉ connectedComponentIn (frontier R) z := by
  intro l u R S hzero hside hphase x hx
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let Q := hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
  let : T2Space X0 := Q.isEmbedding.t2Space
  let : CompactSpace X0 := Q.symm.compactSpace
  have hnot := hamiltonZero_component_frontier_not_subset_single_phase
    hI hd hphi Hbase F ha hb he hfront hinj lower upper hnoA hnoB hgroupsA hgroupsB
    hmin complementary side hK c hr hi hopen hzero hside hphase x hx
  simp only [Set.subset_def, not_forall] at hnot
  obtain ⟨y, hy, hyS⟩ := hnot
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
  have hyF : y ∈ frontier R :=
    ((heR.frontier_connectedComponentIn_of_compact heR.closed.isCompact hx).subset hy).2
  have hyphase : hamiltonZeroCircleMap phi y = (a : C0) ∨
      hamiltonZeroCircleMap phi y = (b : C0) := by
    simpa only [hRfront, mem_preimage, mem_insert_iff, mem_singleton_iff] using hyF
  refine ⟨y, hy, ?_, ?_⟩
  · change hamiltonZeroCircleMap phi y ≠ ((if side then u else l : ℝ) : C0) at hyS
    cases complementary <;> cases side <;>
      simp only [l, u, Bool.false_eq_true, ↓reduceIte, AddCircle.coe_add_period] at hyS ⊢ <;>
      tauto
  · intro z hz hzS hyC
    have heq := isPreconnected_connectedComponentIn.constant_of_mapsTo
      (Set.toFinite ({(a : C0), (b : C0)} : Set C0)).isDiscrete
      (hamiltonZeroCircleMap phi).continuous.continuousOn
      (show MapsTo (hamiltonZeroCircleMap phi) (connectedComponentIn (frontier R) z)
          {(a : C0), (b : C0)} from fun w hw => by
        have hwF := connectedComponentIn_subset (frontier R) z hw
        rwa [hRfront] at hwF)
      hyC (mem_connectedComponentIn hz)
    apply hyS
    change hamiltonZeroCircleMap phi y = _
    exact heq.trans hzS

end PoincareConjecture.M76
