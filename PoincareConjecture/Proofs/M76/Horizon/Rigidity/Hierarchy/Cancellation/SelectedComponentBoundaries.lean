import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.BoundaryComponentObstruction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.ComponentBoundaryGroups
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.Injection









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem IsPLIrreducible.connectedComponentIn
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (hI : IsPLIrreducible e R) (hR : IsCompact R) {x : X} (hx : x ∈ R) :
    IsPLIrreducible e (_root_.connectedComponentIn R x) := by
  refine ⟨hI.1.connectedComponentIn hR hx, ?_⟩
  intro S hS hSphere
  obtain ⟨D, hDR, ⟨ball⟩⟩ := hI.2 S
    (hS.trans (interior_mono (connectedComponentIn_subset R x))) hSphere
  obtain ⟨sphere⟩ := hSphere
  obtain ⟨z, hz⟩ := sphere.isConnected.nonempty
  have hconn : IsPreconnected D := by
    rw [← ball.closure_interior]
    exact ball.isConnected_interior.isPreconnected.closure
  have hDcomp := hconn.subset_connectedComponentIn (ball.boundary_subset hz) hDR
  rw [← connectedComponentIn_eq (interior_subset (hS hz))] at hDcomp
  exact ⟨D, hDcomp, ⟨ball⟩⟩

private theorem select_phase_component
    {X T ι : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace T] [T1Space T]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R N : Set X}
    (q : C(X, T)) (theta other : T)
    (M : FrontierResidualModel e N (q ⁻¹' {theta}))
    (hR : IsClosed R) (hfront : frontier R = q ⁻¹' {theta, other})
    {x : X}
    (hPfront : frontier (connectedComponentIn R x) = connectedComponentIn R x ∩ frontier R)
    (hmeet : (frontier (connectedComponentIn R x) ∩ q ⁻¹' {theta}).Nonempty) :
    ∃ i : Fin M.count, ∃ _z : M.components i,
      M.components i ⊆ frontier (connectedComponentIn R x) ∧
      ∀ y ∈ M.components i,
        connectedComponentIn (frontier (connectedComponentIn R x)) y = M.components i := by
  obtain ⟨z, hzF, hzphase⟩ := hmeet
  obtain ⟨i, hzi⟩ := mem_iUnion.mp (M.cover.symm.subset hzphase)
  have hSF : q ⁻¹' {theta} ⊆ frontier R := by
    rw [hfront]
    exact preimage_mono (singleton_subset_iff.mpr (by simp))
  have hiR := ((M.component i).2.2.1.trans hSF).trans hR.frontier_subset
  have hiP : M.components i ⊆ connectedComponentIn R x := by
    have h := (M.component i).2.1.isPreconnected.subset_connectedComponentIn hzi hiR
    rwa [← connectedComponentIn_eq ((hPfront.subset hzF).1)] at h
  have hiF : M.components i ⊆ frontier (connectedComponentIn R x) := by
    rw [hPfront]
    exact subset_inter hiP ((M.component i).2.2.1.trans hSF)
  refine ⟨i, ⟨z, hzi⟩, hiF, ?_⟩
  intro y hy
  apply subset_antisymm
  · have hsub : connectedComponentIn (frontier (connectedComponentIn R x)) y ⊆ q ⁻¹' {theta} := by
      intro w hw
      have heq := isPreconnected_connectedComponentIn.constant_of_mapsTo
        (Set.toFinite ({theta, other} : Set T)).isDiscrete q.continuous.continuousOn
        (show MapsTo q (connectedComponentIn (frontier (connectedComponentIn R x)) y)
            {theta, other} from fun v hv => by
          have hvF := (hPfront.subset
            (connectedComponentIn_subset (frontier (connectedComponentIn R x)) y hv)).2
          rwa [hfront] at hvF)
        hw (mem_connectedComponentIn (hiF hy))
      exact heq.trans ((M.component i).2.2.1 hy)
    have h := isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (hiF hy)) hsub
    rwa [(M.component i).2.2.2 y hy] at h
  · exact (M.component i).2.1.isPreconnected.subset_connectedComponentIn hy hiF


local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_selected_component_boundaries
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
    (complementary : Bool)
    {E : Type*} [TopologicalSpace E] [T2Space E]
    (K : Bool → Set E) (hK : ∀ s, IsCompact (K s))
    (c : Bool → E × ℝ → X0) {r : ℝ} (hr : 0 < r)
    (hi : ∀ s, Topology.IsEmbedding
      (fun z : (K s ×ˢ Icc (-r) r : Set (E × ℝ)) => c s z))
    (hopen : ∀ s, IsOpen (c s '' (K s ×ˢ Ioo (-r) r))) :
    let l := if complementary then b else a
    let u := if complementary then a + p else b
    let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p l u
    let phase := fun s : Bool =>
      hamiltonZeroCircleMap phi ⁻¹' {((if s then u else l : ℝ) : C0)}
    IsPLIrreducible e R →
    (∀ z : R, Function.Injective (FundamentalGroup.map (VanKampen.inclusion R) z)) →
    (∀ s, ∀ z ∈ K s ×ˢ Icc (-r) r, c s z ∈ R ↔ 0 ≤ z.2) →
    (∀ s, ∀ z ∈ K s ×ˢ Icc (-r) 0, hamiltonZeroCircleMap phi (c s z) =
      ((if s then u - z.2 else l + z.2 : ℝ) : C0)) →
    ∀ (H : ∀ s, K s ≃ₜ phase s) (g : ∀ s, C(K s, C0 × C0)),
      (∀ s, IsCoveringMap (g s)) →
      (∀ s (z : K s), c s (z, 0) = H s z) →
      (∀ s (z : K s), (Q0 (hamiltonZeroAmbientMap phi (c s (z, 0)))).1 = g s z) →
      ∀ x ∈ R,
        let P := connectedComponentIn R x
        IsCompact P ∧ IsConnected P ∧ IsPLIrreducible e P ∧
        (∀ z : P, Function.Injective (FundamentalGroup.map (VanKampen.inclusion P) z)) ∧
        ∃ (iA : Fin lower.count) (iB : Fin upper.count)
          (hAP : lower.components iA ⊆ P) (hBP : upper.components iB ⊆ P),
          Disjoint (lower.components iA) (upper.components iB) ∧
          lower.components iA ⊆ frontier P ∧ upper.components iB ⊆ frontier P ∧
          (∀ y ∈ lower.components iA, connectedComponentIn (frontier P) y = lower.components iA) ∧
          (∀ y ∈ upper.components iB, connectedComponentIn (frontier P) y = upper.components iB) ∧
          IsCoveringMap (hamiltonZeroRetainedTangentialMap phi (lower.components iA)) ∧
          IsCoveringMap (hamiltonZeroRetainedTangentialMap phi (upper.components iB)) ∧
          (∀ z : lower.components iA, Function.Injective
            (FundamentalGroup.map (ContinuousMap.inclusion hAP) z)) ∧
          (∀ z : upper.components iB, Function.Injective
            (FundamentalGroup.map (ContinuousMap.inclusion hBP) z)) ∧
          ∃ (xA : lower.components iA) (xB : upper.components iB),
            let incA := ContinuousMap.inclusion hAP
            let incB := ContinuousMap.inclusion hBP
            (FundamentalGroup.map incA xA).range.FiniteIndex ∧
            (FundamentalGroup.map incB xB).range.FiniteIndex ∧
            ∃ k : Path (incA xA) (incB xB),
              (FundamentalGroup.map incA xA).range.Commensurable
                (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
                  (FundamentalGroup.map incB xB)).range ∧
              ∀ alpha : Path xA xA, ∃ n : ℕ, 0 < n ∧ ∃ beta : Path xB xB,
                ((boundaryLoopIterate alpha n).map incA.continuous).Homotopic
                  (k.trans ((beta.map incB.continuous).trans k.symm)) := by
  intro l u R phase hIR hinjR hside hphase H g hg hzero htangent x hx P
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := (Q0).symm.compactSpace
  have ha0 : 0 < a := by linarith [ha.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have hbp : b < p := by linarith [hb.2]
  have hcomp := circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap phi)
    ha0 hab hbp hfront
  have hRfront : frontier R = hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)} := by
    cases complementary
    · exact hfront
    · simpa only [R, l, u, ↓reduceIte, hcomp] using he.compl_interior.2.trans hfront
  have hPc : IsCompact P := Set.isCompact_connectedComponentIn_of_mem hIR.1.closed.isCompact hx
  have hPconn : IsConnected P := isConnected_connectedComponentIn_iff.mpr hx
  have hIP : IsPLIrreducible e P := hIR.connectedComponentIn hIR.1.closed.isCompact hx
  have hPR : P ⊆ R := connectedComponentIn_subset R x
  have hPfront : frontier P = P ∩ frontier R :=
    hIR.1.frontier_connectedComponentIn_of_compact hIR.1.closed.isCompact hx
  have hinjP : ∀ z : P, Function.Injective
      (FundamentalGroup.map (VanKampen.inclusion P) z) := by
    intro z
    have heq : VanKampen.inclusion P =
        (VanKampen.inclusion R).comp (ContinuousMap.inclusion hPR) := rfl
    rw [heq, FundamentalGroup.map_comp]
    exact (hinjR _).comp (FundamentalGroup.inclusion_injective_of_whole_component hPR
      (fun y hy => (connectedComponentIn_eq hy).symm) z)
  have hzeroImage (s : Bool) : c s '' (K s ×ˢ ({0} : Set ℝ)) = phase s := by
    ext y
    constructor
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      rw [hzero s ⟨z, hz⟩]
      exact (H s ⟨z, hz⟩).property
    · intro hy
      let z := (H s).symm ⟨y, hy⟩
      exact ⟨(z, 0), ⟨z.property, rfl⟩,
        (hzero s z).trans (congrArg Subtype.val ((H s).apply_symm_apply ⟨y, hy⟩))⟩
  have hother (s : Bool) : ∃ y ∈ frontier P,
      hamiltonZeroCircleMap phi y = ((if s then l else u : ℝ) : C0) := by
    obtain ⟨y, hy, heq, _⟩ := hamiltonZero_component_has_other_boundary_phase
      hI hd hphi Hbase F ha hb he hfront hinj lower upper hnoA hnoB hgroupsA hgroupsB
      hmin complementary s (hK s) (c s) hr (hi s) (hopen s) (hzeroImage s)
      (hside s) (hphase s) x hx
    exact ⟨y, hy, heq⟩
  have hmeetA : (frontier P ∩ hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}).Nonempty := by
    cases complementary
    · obtain ⟨y, hy, heq⟩ := hother true
      exact ⟨y, hy, heq⟩
    · obtain ⟨y, hy, heq⟩ := hother false
      exact ⟨y, hy, by simpa [u, AddCircle.coe_add_period] using heq⟩
  have hmeetB : (frontier P ∩ hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}).Nonempty := by
    cases complementary
    · obtain ⟨y, hy, heq⟩ := hother false
      exact ⟨y, hy, heq⟩
    · obtain ⟨y, hy, heq⟩ := hother true
      exact ⟨y, hy, heq⟩
  obtain ⟨iA, xA, hAF, hAwhole⟩ := select_phase_component
    (hamiltonZeroCircleMap phi) (a : C0) (b : C0) lower hIR.1.closed hRfront hPfront hmeetA
  have hRfront' : frontier R = hamiltonZeroCircleMap phi ⁻¹' {(b : C0), (a : C0)} := by
    simpa only [pair_comm] using hRfront
  obtain ⟨iB, xB, hBF, hBwhole⟩ := select_phase_component
    (hamiltonZeroCircleMap phi) (b : C0) (a : C0) upper hIR.1.closed hRfront' hPfront hmeetB
  have hAP := hAF.trans hIP.1.closed.frontier_subset
  have hBP := hBF.trans hIP.1.closed.frontier_subset
  have hane : (a : C0) ≠ (b : C0) := by
    intro heq
    have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) from ⟨ha0.le, by linarith⟩)
      (show b ∈ Ico (0 : ℝ) (0 + p) from ⟨by linarith, by linarith⟩)).mp heq
    exact hab.ne h
  have hdis : Disjoint (lower.components iA) (upper.components iB) :=
    disjoint_left.mpr fun y hyA hyB => hane
      (((lower.component iA).2.2.1 hyA).symm.trans ((upper.component iB).2.2.1 hyB))
  have hwholeCover (s : Bool) : IsCoveringMap (hamiltonZeroRetainedTangentialMap phi (phase s)) := by
    have hfun : (hamiltonZeroRetainedTangentialMap phi (phase s) : phase s → C0 × C0) =
        g s ∘ (H s).symm := by
      funext y
      have hv := htangent s ((H s).symm y)
      rw [hzero, (H s).apply_symm_apply] at hv
      exact hv
    rw [hfun]
    exact (hg s).comp_homeomorph (H s).symm
  have hcoverA : IsCoveringMap
      (hamiltonZeroRetainedTangentialMap phi (lower.components iA)) := by
    apply lower.isCoveringMap_component (hamiltonZeroRetainedTangentialMap phi _) _ iA
    cases complementary
    · exact hwholeCover false
    · have h := hwholeCover true
      change IsCoveringMap (hamiltonZeroRetainedTangentialMap phi
        (hamiltonZeroCircleMap phi ⁻¹' {((a + p : ℝ) : C0)})) at h
      rw [AddCircle.coe_add_period p a] at h
      exact h
  have hcoverB : IsCoveringMap
      (hamiltonZeroRetainedTangentialMap phi (upper.components iB)) := by
    apply upper.isCoveringMap_component (hamiltonZeroRetainedTangentialMap phi _) _ iB
    cases complementary
    · exact hwholeCover true
    · exact hwholeCover false
  have hboundaryInj {S : Set X0} (hSF : S ⊆ frontier P)
      (hwhole : ∀ z ∈ S, connectedComponentIn (frontier P) z = S)
      (hSP : S ⊆ P) (z : S) :
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSP) z) := by
    have hPF : frontier P ⊆ frontier R := fun y hy => (hPfront.subset hy).2
    have hSFold := hSF.trans hPF
    have hwholeOld (y : X0) (hy : y ∈ S) : connectedComponentIn (frontier R) y = S := by
      have hFR : frontier R ⊆ R := hIR.1.closed.frontier_subset
      have hCyP : connectedComponentIn (frontier R) y ⊆ P := by
        have h := connectedComponentIn_mono y hFR
        rwa [← connectedComponentIn_eq (hSP hy)] at h
      have hCyFP : connectedComponentIn (frontier R) y ⊆ frontier P := by
        rw [hPfront]
        exact subset_inter hCyP (connectedComponentIn_subset _ _)
      have h := isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (hSFold hy)) hCyFP
      rw [hwhole y hy] at h
      exact subset_antisymm h ((hwhole y hy).symm ▸ connectedComponentIn_mono y hPF)
    have hFRinj : ∀ w : frontier R, Function.Injective
        (FundamentalGroup.map (VanKampen.inclusion (frontier R)) w) := by
      rw [hRfront.trans hfront.symm]
      exact hinj
    have hamb : Function.Injective (FundamentalGroup.map (VanKampen.inclusion S) z) := by
      change Function.Injective (FundamentalGroup.map
        ((VanKampen.inclusion (frontier R)).comp (ContinuousMap.inclusion hSFold)) z)
      rw [FundamentalGroup.map_comp]
      exact (hFRinj _).comp
        (FundamentalGroup.inclusion_injective_of_whole_component hSFold hwholeOld z)
    change Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion hSP) z)
    have hfactor : VanKampen.inclusion S =
        (VanKampen.inclusion P).comp (ContinuousMap.inclusion hSP) := rfl
    rw [hfactor, FundamentalGroup.map_comp] at hamb
    exact Function.Injective.of_comp hamb
  refine ⟨hPc, hPconn, hIP, hinjP, iA, iB, hAP, hBP, hdis, hAF, hBF,
    hAwhole, hBwhole, hcoverA, hcoverB, hboundaryInj hAF hAwhole hAP,
    hboundaryInj hBF hBwhole hBP, xA, xB, ?_⟩
  let incA := ContinuousMap.inclusion hAP
  let incB := ContinuousMap.inclusion hBP
  let : CompactSpace (lower.components iA) := isCompact_iff_compactSpace.mp (lower.component iA).1
  let : CompactSpace (upper.components iB) := isCompact_iff_compactSpace.mp (upper.component iB).1
  let : ConnectedSpace P := isConnected_iff_connectedSpace.mp hPconn
  let : LocallyPathConnectedSpace P := hIP.1.locallyPathConnectedSpace
  let : PathConnectedSpace P := PathConnectedSpace.of_locallyPathConnectedSpace
  let k : Path (incA xA) (incB xB) := PathConnectedSpace.somePath _ _
  have hnormal : ∀ z : P, Function.Injective
      (FundamentalGroup.map (hamiltonZeroRetainedTangentialMap phi P) z) := by
    intro z
    apply hamiltonZeroRetainedTangentialMap_pi1_injective phi F
      (cut := if complementary then (a + b) / 2 else 0)
      (a := l) (b := u) _ _ _ hPR z (hinjP z)
    all_goals cases complementary <;> dsimp [l, u] <;> linarith
  have hidxA := boundary_group_finiteIndex_of_covering_composite incA
    (hamiltonZeroRetainedTangentialMap phi P) hcoverA xA (hnormal _)
  have hidxB := boundary_group_finiteIndex_of_covering_composite incB
    (hamiltonZeroRetainedTangentialMap phi P) hcoverB xB (hnormal _)
  have hcomm := boundary_groups_commensurable_of_finiteIndex incA incB xA xB hidxA hidxB k
  exact ⟨hidxA, hidxB, k, hcomm,
    fun alpha => exists_boundary_loop_power_homotopy incA incB xA xB k hcomm alpha⟩

end PoincareConjecture.M76
