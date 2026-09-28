import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.MarkedDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.SourceCollarCoordinates

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem phase_interior_isOpen_frontier
    {N A A' F : Set X} (hfront : frontier N = (N ∩ F) ∪ (A ∪ A'))
    (hAB : Disjoint A A') (hB : IsClosed A') (hF : IsClosed F) :
    IsOpen ((Subtype.val : frontier N → X) ⁻¹' (A \ F)) := by
  have heq : (Subtype.val : frontier N → X) ⁻¹' (A \ F) =
      (Subtype.val : frontier N → X) ⁻¹' (F ∪ A')ᶜ := by
    ext x
    change (x.val ∈ A ∧ x.val ∉ F) ↔ x.val ∉ F ∪ A'
    constructor
    · rintro ⟨ha, hf⟩ (hf' | hb)
      · exact hf hf'
      · exact disjoint_left.mp hAB ha hb
    · intro hx
      have hf : x.val ∉ F := fun hf => hx (Or.inl hf)
      have hb : x.val ∉ A' := fun hb => hx (Or.inr hb)
      have hmem := hfront.subset x.property
      exact ⟨hmem.elim (fun h => (hf h.2).elim) (fun h => h.resolve_right hb), hf⟩
  rw [heq]
  exact (hF.union hB).isOpen_compl.preimage continuous_subtype_val

theorem exists_sourceSlab_relative_compression_disks
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      IsCompact (sourceSlab phi a b) ∧ PLDomain e (sourceSlab phi a b) ∧
      frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)) ∧
      Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) ∧
      ∀ theta ∈ ({a, b} : Set ℝ),
        let S := sourceSurface phi (theta : C)
        let M := S \ frontier R
        ∃ hMN : M ⊆ sourceSlab phi a b,
          ∀ x : M,
            (∀ c : FundamentalGroup M x,
              FundamentalGroup.map (ContinuousMap.inclusion hMN) x c = 1 →
                FundamentalGroup.map (ContinuousMap.inclusion sdiff_subset) x c = 1) ∨
            ∃ (j : V2 → X) (rim : C(Q, M)),
              PolyhedralPLInCharts e j D ∧
              Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D (sourceSlab phi a b) ∧
              (∀ z : Q, j z = (rim z : X)) ∧
              (∀ z : D, j z ∈ frontier (sourceSlab phi a b) ↔ (z : V2) ∈ Q) ∧
              (∀ z : D, j z ∉ frontier R) ∧
              FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
                ((Dehn.squareRimLoop.map rim.continuous).map
                  (ContinuousMap.inclusion (sdiff_subset : M ⊆ S)).continuous)) ≠ 1 := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  obtain ⟨a, ha, b, hb, hN, he, hfront, hAB, hcompact, _⟩ :=
    exists_sourceSlab_with_marked_corners e d hd phi hphi F
  have hab : a < b := by linarith [ha.2, hb.1]
  refine ⟨a, ha, b, hb, hN, he, hfront, hAB, ?_⟩
  intro theta htheta
  let S := sourceSurface phi (theta : C)
  let M := S \ frontier R
  have htI : theta ∈ Icc a b := by
    rcases htheta with rfl | rfl
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
  have hMN : M ⊆ sourceSlab phi a b :=
    sdiff_subset.trans (sourceSurface_subset_slab phi htI)
  have hMfront : M ⊆ frontier (sourceSlab phi a b) := by
    intro x hx
    rw [hfront]
    right
    rcases htheta with rfl | rfl
    · exact Or.inl hx.1
    · exact Or.inr hx.1
  have hMopen : IsOpen ((Subtype.val : frontier (sourceSlab phi a b) → X) ⁻¹' M) := by
    rcases htheta with rfl | rfl
    · exact phase_interior_isOpen_frontier hfront hAB
        (hcompact b (by simp)).1.isClosed isClosed_frontier
    · have hfront' := hfront.trans (congrArg ((sourceSlab phi a theta ∩ frontier R) ∪ ·)
        (union_comm (sourceSurface phi (a : C)) (sourceSurface phi (theta : C))))
      exact phase_interior_isOpen_frontier hfront' hAB.symm
        (hcompact a (by simp)).1.isClosed isClosed_frontier
  refine ⟨hMN, ?_⟩
  intro x
  obtain hker | ⟨j, rim, hj, hi, hjN, hjrim, hproper, hessential⟩ :=
    kernel_le_or_exists_marked_disk e he hMN hMfront hMopen
      (ContinuousMap.inclusion (sdiff_subset : M ⊆ S)) x
  · exact Or.inl hker
  · refine Or.inr ⟨j, rim, hj, hi, hjN, hjrim, hproper, ?_, hessential⟩
    intro z hz
    have hzfront : j z ∈ frontier (sourceSlab phi a b) := by
      rw [hfront]
      exact Or.inl ⟨hjN z.property, hz⟩
    have hzQ := (hproper z).mp hzfront
    have heq := hjrim ⟨z, hzQ⟩
    exact (rim ⟨z, hzQ⟩).property.2 (heq ▸ hz)

end PoincareConjecture.M76.HamiltonIntervalTorus
