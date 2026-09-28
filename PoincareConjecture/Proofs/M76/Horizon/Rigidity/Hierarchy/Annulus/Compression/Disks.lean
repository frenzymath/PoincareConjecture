import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.MarkedDisk

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
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

private theorem new_phase_open_in_frontier
    {N A B F : Set X0} (hfront : frontier N = (N ∩ F) ∪ (A ∪ B))
    (hAB : Disjoint A B) (hB : IsClosed B) (hF : IsClosed F) :
    IsOpen ((Subtype.val : frontier N → X0) ⁻¹' (A \ F)) := by
  have heq : (Subtype.val : frontier N → X0) ⁻¹' (A \ F) =
      (Subtype.val : frontier N → X0) ⁻¹' (F ∪ B)ᶜ := by
    ext x
    change (x.val ∈ A ∧ x.val ∉ F) ↔ x.val ∉ F ∪ B
    constructor
    · rintro ⟨ha, hf⟩ (hf' | hb)
      · exact hf hf'
      · exact disjoint_left.mp hAB ha hb
    · intro hx
      have hf : x.val ∉ F := fun hf => hx (Or.inl hf)
      have hb : x.val ∉ B := fun hb => hx (Or.inr hb)
      exact ⟨(hfront.subset x.property).elim (fun h => (hf h.2).elim)
        (fun h => h.resolve_right hb), hf⟩
  rw [heq]
  exact (hF.union hB).isOpen_compl.preimage continuous_subtype_val

theorem hamiltonZero_second_slab_disk_alternative {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (phi : C(H0, H0))
    {R : Set X0} (hR : IsClosed R) {a b : ℝ}
    (hPL : PLDomain e (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(b : C0)})))
    (hAB : Disjoint (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)})
      (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(b : C0)})) :
    let q := hamiltonZeroSecondCircleMap phi
    let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b
    ∀ theta ∈ ({a, b} : Set ℝ),
      let S := R ∩ q ⁻¹' {(theta : C0)}
      let M := S \ frontier R
      ∃ hMN : M ⊆ N, ∀ x : M,
        (∀ gamma : FundamentalGroup M x,
          FundamentalGroup.map (ContinuousMap.inclusion hMN) x gamma = 1 →
            FundamentalGroup.map (ContinuousMap.inclusion (sdiff_subset : M ⊆ S)) x gamma = 1) ∨
        ∃ (j : V2 → X0) (rim : C(Q, M)),
          PolyhedralPLInCharts e j D ∧
          Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D N ∧
          (∀ z : Q, j z = (rim z : X0)) ∧
          (∀ z : D, j z ∈ frontier N ↔ (z : V2) ∈ Q) ∧
          (∀ z : D, j z ∉ frontier R) ∧
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            ((Dehn.squareRimLoop.map rim.continuous).map
              (ContinuousMap.inclusion (sdiff_subset : M ⊆ S)).continuous)) ≠ 1 := by
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  intro q N theta htheta
  let S := R ∩ q ⁻¹' {(theta : C0)}
  let M := S \ frontier R
  have hclosed (t : C0) : IsClosed (R ∩ q ⁻¹' {t}) :=
    hR.inter (isClosed_singleton.preimage q.continuous)
  have hMF : M ⊆ frontier N := by
    intro x hx
    rw [hfront]
    right
    rcases htheta with rfl | rfl
    · exact Or.inl hx.1
    · exact Or.inr hx.1
  have hMN : M ⊆ N := hMF.trans hPL.closed.frontier_subset
  have hMopen : IsOpen ((Subtype.val : frontier N → X0) ⁻¹' M) := by
    rcases htheta with rfl | rfl
    · exact new_phase_open_in_frontier hfront hAB (hclosed _) isClosed_frontier
    · rw [union_comm (R ∩ q ⁻¹' {(a : C0)})] at hfront
      exact new_phase_open_in_frontier hfront hAB.symm (hclosed _) isClosed_frontier
  refine ⟨hMN, ?_⟩
  intro x
  obtain hker | ⟨j, rim, hj, hi, hjN, hjrim, hproper, hessential⟩ :=
    HamiltonIntervalTorus.kernel_le_or_exists_marked_disk e hPL hMN hMF hMopen
      (ContinuousMap.inclusion (sdiff_subset : M ⊆ S)) x
  · exact Or.inl hker
  · refine Or.inr ⟨j, rim, hj, hi, hjN, hjrim, hproper, ?_, hessential⟩
    intro z hz
    have hzfront := hfront.symm.subset (Or.inl ⟨hjN z.property, hz⟩)
    have hzQ := (hproper z).mp hzfront
    exact (rim ⟨z, hzQ⟩).property.2 ((hjrim ⟨z, hzQ⟩) ▸ hz)

theorem exists_hamiltonZero_second_slab_compression_disks {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      let q := hamiltonZeroSecondCircleMap phi
      let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b
      IsCompact N ∧ PLDomain e N ∧
      frontier N = (N ∩ frontier R) ∪ (R ∩ q ⁻¹' {(a : C0), (b : C0)}) ∧
      ∀ theta ∈ ({a, b} : Set ℝ),
        let S := R ∩ q ⁻¹' {(theta : C0)}
        let M := S \ frontier R
        ∃ hMN : M ⊆ N, ∀ x : M,
          (∀ c : FundamentalGroup M x,
            FundamentalGroup.map (ContinuousMap.inclusion hMN) x c = 1 →
              FundamentalGroup.map (ContinuousMap.inclusion (sdiff_subset : M ⊆ S)) x c = 1) ∨
          ∃ (j : V2 → X0) (rim : C(Q, M)),
            PolyhedralPLInCharts e j D ∧
            Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D N ∧
            (∀ z : Q, j z = (rim z : X0)) ∧
            (∀ z : D, j z ∈ frontier N ↔ (z : V2) ∈ Q) ∧
            (∀ z : D, j z ∉ frontier R) ∧
            FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
              ((Dehn.squareRimLoop.map rim.continuous).map
                (ContinuousMap.inclusion (sdiff_subset : M ⊆ S)).continuous)) ≠ 1 := by
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨a, ha, b, hb, hN, hPL, hfront, hAB, _⟩ :=
    exists_hamiltonZero_second_coordinate_slab e d hd phi hphi he
  let q := hamiltonZeroSecondCircleMap phi
  let N := R ∩ q ⁻¹' AddCircle.closedIntervalArc p a b
  have hfront' : frontier N = (N ∩ frontier R) ∪
      ((R ∩ q ⁻¹' {(a : C0)}) ∪ (R ∩ q ⁻¹' {(b : C0)})) := by
    rw [hfront]
    ext x
    simp only [mem_union, mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff]
    tauto
  exact ⟨a, ha, b, hb, hN, hPL, hfront,
    hamiltonZero_second_slab_disk_alternative e phi he.closed hPL hfront' hAB⟩

end PoincareConjecture.M76
