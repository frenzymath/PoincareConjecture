import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.CollarEnlargement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.RetainedSlab









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_compact_same_phase_cancellation_region
    {E X : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X] {p : ℝ} [Fact (0 < p)]
    (q : C(X, AddCircle p)) {cut a b : ℝ}
    (ha : cut < a) (hab : a < b) (hb : b < cut + p)
    {P : Set X} (hP : IsCompact P)
    (hPphase : P ⊆ q ⁻¹' AddCircle.closedIntervalArc p a b)
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (c : E × ℝ → X) {r : ℝ} (hr : 0 < r) (side : Bool)
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier P)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ P ↔ 0 ≤ z.2)
    (hopen : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    (hphase : ∀ z ∈ K ×ˢ Icc (-r) 0,
      q (c z) = ((if side then b - z.2 else a + z.2 : ℝ) : AddCircle p)) :
    ∃ (D : Set X) (u v lambda : ℝ),
      IsCompact D ∧ P ⊆ interior D ∧ cut < u ∧ v < cut + p ∧ lambda ∈ Icc u v ∧
      (a : AddCircle p) ≠ (lambda : AddCircle p) ∧
      (b : AddCircle p) ≠ (lambda : AddCircle p) ∧
      D ⊆ q ⁻¹' AddCircle.closedIntervalArc p u v ∧
      (∀ x ∈ frontier D, q x = (lambda : AddCircle p)) ∧
      ((q ⁻¹' {(a : AddCircle p), (b : AddCircle p)}) ∩ interior D).Nonempty := by
  let eps := min r (min (a - cut) (cut + p - b)) / 2
  have heps : 0 < eps := half_pos (lt_min hr (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)))
  have hepsr : eps < r := by
    have : 2 * eps ≤ r := by
      dsimp [eps]
      linarith [min_le_left r (min (a - cut) (cut + p - b))]
    linarith
  have hepsa : eps < a - cut := by
    have := (min_le_right r (min (a - cut) (cut + p - b))).trans
      (min_le_left (a - cut) (cut + p - b))
    dsimp [eps] at *
    linarith
  have hepsb : eps < cut + p - b := by
    have := (min_le_right r (min (a - cut) (cut + p - b))).trans
      (min_le_right (a - cut) (cut + p - b))
    dsimp [eps] at *
    linarith
  let D := P ∪ c '' (K ×ˢ Icc (-eps) 0)
  let lambda := if side then b + eps else a - eps
  have hu : cut < a - eps := by linarith
  have hv : b + eps < cut + p := by linarith
  have hlambda : lambda ∈ Icc (a - eps) (b + eps) := by
    cases side <;> dsimp [lambda] <;> constructor <;> linarith
  have hlambdaI : lambda ∈ Ico cut (cut + p) :=
    ⟨(hu.le.trans hlambda.1), by linarith [hlambda.2]⟩
  have hane : (a : AddCircle p) ≠ (lambda : AddCircle p) := by
    intro h
    have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico cut (cut + p) from ⟨ha.le, by linarith⟩) hlambdaI).mp h
    cases side <;> dsimp [lambda] at h <;> linarith
  have hbne : (b : AddCircle p) ≠ (lambda : AddCircle p) := by
    intro h
    have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show b ∈ Ico cut (cut + p) from ⟨by linarith, hb⟩) hlambdaI).mp h
    cases side <;> dsimp [lambda] at h <;> linarith
  obtain ⟨hD, hPi, hfront⟩ := compact_signed_collar_enlargement hP hK c heps hepsr
    (continuousOn_iff_continuous_domRestrict.mpr hi.continuous) hi hzero hside hopen
  have hsmall : K ×ˢ Icc (-eps) 0 ⊆ K ×ˢ Icc (-r) 0 := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
  refine ⟨D, a - eps, b + eps, lambda, hD, hPi, hu, hv, hlambda, hane, hbne, ?_, ?_, ?_⟩
  · rintro x (hx | ⟨z, hz, rfl⟩)
    · obtain ⟨t, ht, htq⟩ := hPphase hx
      exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, htq⟩
    · change q (c z) ∈ AddCircle.closedIntervalArc p (a - eps) (b + eps)
      rw [hphase z (hsmall hz)]
      refine ⟨if side then b - z.2 else a + z.2, ?_, rfl⟩
      cases side <;> dsimp <;> constructor <;> linarith [hz.2.1, hz.2.2]
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hfront.subset hx
    have ht : z.2 = -eps := hz.2
    rw [hphase z (hsmall ⟨hz.1, by rw [ht]; exact ⟨le_rfl, neg_nonpos.mpr heps.le⟩⟩), ht]
    cases side <;> simp [lambda, sub_eq_add_neg]
  · obtain ⟨z, hz⟩ := hne
    refine ⟨c (z, 0), ?_, hPi (hP.isClosed.frontier_subset
      (hzero.subset ⟨(z, 0), ⟨hz, rfl⟩, rfl⟩))⟩
    change q (c (z, 0)) = (a : AddCircle p) ∨ q (c (z, 0)) = (b : AddCircle p)
    rw [hphase (z, 0) ⟨hz, by linarith, le_rfl⟩]
    cases side <;> simp

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_smaller_phase_count_of_collared_region
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
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {P : Set X0} (hP : IsCompact P)
    (hPphase : P ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (c : E × ℝ → X0) {r : ℝ} (hr : 0 < r) (side : Bool)
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier P)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ P ↔ 0 ≤ z.2)
    (hopen : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    (hphase : ∀ z ∈ K ×ˢ Icc (-r) 0,
      hamiltonZeroCircleMap phi (c z) = ((if side then b - z.2 else a + z.2 : ℝ) : C0)) :
    ∃ m, HamiltonZeroIncompressiblePhaseCount e d base m ∧ m < lower.count + upper.count := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨D, u, v, lambda, hD, _, hu, hv, hlambda, haLambda, hbLambda, hrange,
      hDfront, hmeet⟩ :=
    exists_compact_same_phase_cancellation_region (cut := 0) (hamiltonZeroCircleMap phi)
      (by linarith [ha.1]) (by linarith [ha.2, hb.1]) (by linarith [hb.2])
      hP hPphase hK hne c hr side hi hzero hside hopen hphase
  exact exists_hamiltonZero_smaller_phase_count_of_closed_region hI hd hphi Hbase F
    ha hb he hfront hinj lower upper hnoA hnoB hgroupsA hgroupsB hD.isClosed
    (cut := 0) hu (by simpa using hv) hlambda haLambda hbLambda hrange hDfront
    (hmeet.mono (inter_subset_inter_right _ interior_subset))

theorem exists_hamiltonZero_smaller_phase_count_of_complementary_collared_region
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
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {P : Set X0} (hP : IsCompact P)
    (hPphase : P ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p b (a + p))
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (c : E × ℝ → X0) {r : ℝ} (hr : 0 < r) (side : Bool)
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier P)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ P ↔ 0 ≤ z.2)
    (hopen : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    (hphase : ∀ z ∈ K ×ˢ Icc (-r) 0,
      hamiltonZeroCircleMap phi (c z) =
        ((if side then a + p - z.2 else b + z.2 : ℝ) : C0)) :
    ∃ m, HamiltonZeroIncompressiblePhaseCount e d base m ∧ m < lower.count + upper.count := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨D, u, v, lambda, hD, _, hu, hv, hlambda, hbLambda, haLambda, hrange,
      hDfront, hmeet⟩ :=
    exists_compact_same_phase_cancellation_region (cut := (a + b) / 2)
      (hamiltonZeroCircleMap phi)
      (by linarith [ha.2, hb.1]) (by linarith [ha.1, hb.2])
      (by linarith [ha.2, hb.1]) hP hPphase hK hne c hr side hi hzero hside hopen hphase
  have haLambda' : (a : C0) ≠ (lambda : C0) := by
    simpa only [AddCircle.coe_add_period] using haLambda
  apply exists_hamiltonZero_smaller_phase_count_of_closed_region hI hd hphi Hbase F
    ha hb he hfront hinj lower upper hnoA hnoB hgroupsA hgroupsB hD.isClosed
    hu hv hlambda haLambda' hbLambda hrange hDfront
  obtain ⟨x, hx, hxD⟩ := hmeet
  refine ⟨x, ?_, interior_subset hxD⟩
  rcases hx with hx | hx
  · exact Or.inr hx
  · exact Or.inl (by simpa only [mem_singleton_iff, AddCircle.coe_add_period] using hx)

end PoincareConjecture.M76
