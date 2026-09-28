import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Compression.OriginalWideSlabCompression
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Compression.OriginalWideUpperSlabCompression
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.ResidualCompressionDecrease
import PoincareConjecture.Proofs.M76.Rigidity.OriginalHandleHomotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalRelativeStripFrontier

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

theorem ChartwisePLMap.exists_hamiltonZero_wide_lower_residual_decrease {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + 64)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)})
    {Nold : Set X0} (oldModel : FrontierResidualModel e Nold
      (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}))
    {j : V2 → X0} (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b))
    (hproper : ∀ z : D, j z ∈ frontier
      (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ↔ (z : V2) ∈ Q)
    (rim : C(Q, hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}))
    (hrim : ∀ z : Q, j z = (rim z : X0))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      PLDomain e (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ∧
      frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) =
        hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} ∧
      hamiltonZeroCircleMap psi ⁻¹' {(b : C0)} = hamiltonZeroCircleMap phi ⁻¹' {(b : C0)} ∧
      (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ⊆
        (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ∧
      ∃ newModel : FrontierResidualModel e
        (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b)
        (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}),
        newModel.complexity < oldModel.complexity := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b
  have hphase (z : V2) (hz : z ∈ Q) : hamiltonZeroCircleMap phi (j z) = (a : C0) := by
    rw [hrim ⟨z, hz⟩]
    exact (rim ⟨z, hz⟩).property
  obtain ⟨P, G, N, hcut, hcompact, _, _, _, _, _, _, hGa, hGb, hlateral,
    havoid, hGslab, _, hnewfront, hGtail⟩ :=
    hphi.exists_hamiltonZero_wide_lower_slab_compression hd F ha hab hb he hfront
      hj hemb hDR hproper hphase
  let f : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let psi := hamiltonZeroHandleMap f
  have hq : (hamiltonZeroCircleMap psi : X0 → C0) = (fun x => (Q0 (G (1, x))).2) := by
    funext x
    change (Q0 (hamiltonZeroAmbientMap (hamiltonZeroHandleMap f) x)).2 = _
    rw [hamiltonZeroAmbientMap_handle]
    rfl
  obtain ⟨hpsi, H, ⟨Fpsi⟩⟩ := hGtail
  have hslab : hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b =
      P.cutCarrier := hq ▸ hGslab
  have hnewfront' : frontier P.cutCarrier = hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} :=
    hq ▸ hnewfront
  have hnewphase := hq ▸ hGa
  have hupper : hamiltonZeroCircleMap psi ⁻¹' {(b : C0)} =
      hamiltonZeroCircleMap phi ⁻¹' {(b : C0)} := hq ▸ hGb 1
  have habq : (a : C0) ≠ (b : C0) := by
    intro h
    have haI : a ∈ Ico c (c + 4 * 16) := ⟨ha.le, by linarith⟩
    have hbI : b ∈ Ico c (c + 4 * 16) := ⟨by linarith, by linarith⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp h)
  have hsplit : frontier R = (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}) ∪
      (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}) := by
    rw [hfront]
    ext x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, mem_union]
    exact or_comm
  have hcutU : (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)})ᶜ ∩ frontier R =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0)} := by
    rw [hsplit]
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_union, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact (hx h).elim
      · exact h
    · intro hx
      exact ⟨fun hxb => habq (hx.symm.trans hxb), Or.inr hx⟩
  have hcontain : hamiltonZeroCircleMap phi ⁻¹' {(a : C0)} ∪ P.closedStrip ⊆ R := by
    rintro x (hx | hx)
    · exact he.closed.frontier_subset (by rw [hsplit]; exact Or.inr hx)
    · exact P.closedStrip_subset hx
  have hnewsplit : frontier P.cutCarrier = (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}) ∪
      (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}) := by
    rw [hnewfront']
    ext x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, mem_union]
    exact or_comm
  have hnewdis : Disjoint (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)})
      (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}) := by
    exact Set.disjoint_left.mpr (fun x hxb hxa => habq (hxa.symm.trans hxb))
  have hnewne : (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}).Nonempty := by
    obtain ⟨x, hx⟩ := surjective_hamiltonZeroCircleMap psi Fpsi (a : C0)
    exact ⟨x, hx⟩
  have hnewinside : hamiltonZeroCircleMap psi ⁻¹' {(a : C0)} ⊆ P.cutCarrier := by
    intro x hx
    exact hcut.closed.frontier_subset (by rw [hnewsplit]; exact Or.inr hx)
  obtain ⟨newModel⟩ := hcut.nonempty_frontier_residual_model hcompact
    (hnewne.mono hnewinside)
    (isClosed_singleton.preimage (hamiltonZeroCircleMap psi).continuous)
    (isClosed_singleton.preimage (hamiltonZeroCircleMap psi).continuous)
    hnewdis hnewsplit hnewne
  have hdecrease := P.frontierResidualModel_complexity_decreases hcutU havoid hlateral
    hnewphase he he.closed.isCompact hcontain hnewinside rim (fun z => (hrim z).symm)
    hessential oldModel newModel
  refine ⟨psi, hpsi, H, ⟨Fpsi⟩, hslab ▸ hcut, ?_, hupper, ?_, ?_⟩
  · rw [hslab]
    exact hnewfront'
  · rw [hslab]
    exact sdiff_subset
  · rw [hslab]
    exact ⟨newModel, hdecrease⟩

theorem ChartwisePLMap.exists_hamiltonZero_wide_upper_residual_decrease {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + 64)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)})
    {Nold : Set X0} (oldModel : FrontierResidualModel e Nold
      (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}))
    {j : V2 → X0} (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b))
    (hproper : ∀ z : D, j z ∈ frontier
      (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ↔ (z : V2) ∈ Q)
    (rim : C(Q, hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}))
    (hrim : ∀ z : Q, j z = (rim z : X0))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      PLDomain e (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ∧
      frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) =
        hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} ∧
      hamiltonZeroCircleMap psi ⁻¹' {(a : C0)} = hamiltonZeroCircleMap phi ⁻¹' {(a : C0)} ∧
      (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ⊆
        (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b) ∧
      ∃ newModel : FrontierResidualModel e
        (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b)
        (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}),
        newModel.complexity < oldModel.complexity := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b
  have hphase (z : V2) (hz : z ∈ Q) : hamiltonZeroCircleMap phi (j z) = (b : C0) := by
    rw [hrim ⟨z, hz⟩]
    exact (rim ⟨z, hz⟩).property
  obtain ⟨P, G, N, hcut, hcompact, _, _, _, _, _, _, hGa, hGb, hlateral,
    havoid, hGslab, _, hnewfront, hGtail⟩ :=
    hphi.exists_hamiltonZero_wide_upper_slab_compression hd F ha hab hb he hfront
      hj hemb hDR hproper hphase
  let f : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let psi := hamiltonZeroHandleMap f
  have hq : (hamiltonZeroCircleMap psi : X0 → C0) = (fun x => (Q0 (G (1, x))).2) := by
    funext x
    change (Q0 (hamiltonZeroAmbientMap (hamiltonZeroHandleMap f) x)).2 = _
    rw [hamiltonZeroAmbientMap_handle]
    rfl
  obtain ⟨hpsi, H, ⟨Fpsi⟩⟩ := hGtail
  have hslab : hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc (4 * 16) a b =
      P.cutCarrier := hq ▸ hGslab
  have hnewfront' : frontier P.cutCarrier = hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} :=
    hq ▸ hnewfront
  have hnewphase := hq ▸ hGa
  have hupper : hamiltonZeroCircleMap psi ⁻¹' {(a : C0)} =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0)} := hq ▸ hGb 1
  have habq : (b : C0) ≠ (a : C0) := by
    intro h
    have haI : a ∈ Ico c (c + 4 * 16) := ⟨ha.le, by linarith⟩
    have hbI : b ∈ Ico c (c + 4 * 16) := ⟨by linarith, by linarith⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp h.symm)
  have hsplit : frontier R = (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}) ∪
      (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}) := by
    rw [hfront]
    ext x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, mem_union]
  have hcutU : (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)})ᶜ ∩ frontier R =
      hamiltonZeroCircleMap phi ⁻¹' {(b : C0)} := by
    rw [hsplit]
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_union, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact (hx h).elim
      · exact h
    · intro hx
      exact ⟨fun hxb => habq (hx.symm.trans hxb), Or.inr hx⟩
  have hcontain : hamiltonZeroCircleMap phi ⁻¹' {(b : C0)} ∪ P.closedStrip ⊆ R := by
    rintro x (hx | hx)
    · exact he.closed.frontier_subset (by rw [hsplit]; exact Or.inr hx)
    · exact P.closedStrip_subset hx
  have hnewsplit : frontier P.cutCarrier = (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}) ∪
      (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}) := by
    rw [hnewfront']
    ext x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, mem_union]
  have hnewdis : Disjoint (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)})
      (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}) := by
    exact Set.disjoint_left.mpr (fun x hxb hxa => habq (hxa.symm.trans hxb))
  have hnewne : (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)}).Nonempty := by
    obtain ⟨x, hx⟩ := surjective_hamiltonZeroCircleMap psi Fpsi (b : C0)
    exact ⟨x, hx⟩
  have hnewinside : hamiltonZeroCircleMap psi ⁻¹' {(b : C0)} ⊆ P.cutCarrier := by
    intro x hx
    exact hcut.closed.frontier_subset (by rw [hnewsplit]; exact Or.inr hx)
  obtain ⟨newModel⟩ := hcut.nonempty_frontier_residual_model hcompact
    (hnewne.mono hnewinside)
    (isClosed_singleton.preimage (hamiltonZeroCircleMap psi).continuous)
    (isClosed_singleton.preimage (hamiltonZeroCircleMap psi).continuous)
    hnewdis hnewsplit hnewne
  have hdecrease := P.frontierResidualModel_complexity_decreases hcutU havoid hlateral
    hnewphase he he.closed.isCompact hcontain hnewinside rim (fun z => (hrim z).symm)
    hessential oldModel newModel
  refine ⟨psi, hpsi, H, ⟨Fpsi⟩, hslab ▸ hcut, ?_, hupper, ?_, ?_⟩
  · rw [hslab]
    exact hnewfront'
  · rw [hslab]
    exact sdiff_subset
  · rw [hslab]
    exact ⟨newModel, hdecrease⟩

end PoincareConjecture.M76
