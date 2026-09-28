import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.SourceDisks









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
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem sourceSlab_phase_frontier_disk_alternative
    {α : Type*} (e : α → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) {a b : ℝ} {theta theta' : C}
    (he : PLDomain e (sourceSlab phi a b))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta')) :
    let N := sourceSlab phi a b
    let M := sourceSurface phi theta \ frontier R
    ∃ hMF : M ⊆ frontier N, ∀ x : M,
      (∀ c : FundamentalGroup M x,
        FundamentalGroup.map (ContinuousMap.inclusion (hMF.trans he.closed.frontier_subset)) x c = 1 →
          FundamentalGroup.map (ContinuousMap.inclusion hMF) x c = 1) ∨
      ∃ (j : V2 → X) (rim : C(Q, M)),
        PolyhedralPLInCharts e j D ∧
        Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D N ∧
        (∀ z : Q, j z = (rim z : X)) ∧
        (∀ z : D, j z ∈ frontier N ↔ (z : V2) ∈ Q) ∧
        (∀ z : D, j z ∉ frontier R) ∧
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((Dehn.squareRimLoop.map rim.continuous).map
            (ContinuousMap.inclusion hMF).continuous)) ≠ 1 := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let N := sourceSlab phi a b
  let M := sourceSurface phi theta \ frontier R
  have hMF : M ⊆ frontier N := fun _ hx => hfront.symm.subset (Or.inr (Or.inl hx.1))
  have hMopen : IsOpen ((Subtype.val : frontier N → X) ⁻¹' M) :=
    phase_interior_isOpen_frontier hfront hAB (sourceSurface_isCompact phi theta').isClosed
      isClosed_frontier
  refine ⟨hMF, ?_⟩
  intro x
  obtain hker | ⟨j, rim, hj, hi, hjN, hjrim, hproper, hessential⟩ :=
    kernel_le_or_exists_marked_disk e he (hMF.trans he.closed.frontier_subset) hMF hMopen
      (ContinuousMap.inclusion hMF) x
  · exact Or.inl hker
  · refine Or.inr ⟨j, rim, hj, hi, hjN, hjrim, hproper, ?_, hessential⟩
    intro z hz
    have hzfront := hfront.symm.subset (Or.inl ⟨hjN z.property, hz⟩)
    have hzQ := (hproper z).mp hzfront
    exact (rim ⟨z, hzQ⟩).property.2 ((hjrim ⟨z, hzQ⟩) ▸ hz)

theorem sourceSlab_frontier_disk_alternative
    {α : Type*} (e : α → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) {a b : ℝ}
    (he : PLDomain e (sourceSlab phi a b))
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hAB : Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C))) :
    let N := sourceSlab phi a b
    let M := sourceSurface phi (a : C) \ frontier R
    ∃ hMF : M ⊆ frontier N, ∀ x : M,
      (∀ c : FundamentalGroup M x,
        FundamentalGroup.map (ContinuousMap.inclusion (hMF.trans he.closed.frontier_subset)) x c = 1 →
          FundamentalGroup.map (ContinuousMap.inclusion hMF) x c = 1) ∨
      ∃ (j : V2 → X) (rim : C(Q, M)),
        PolyhedralPLInCharts e j D ∧
        Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D N ∧
        (∀ z : Q, j z = (rim z : X)) ∧
        (∀ z : D, j z ∈ frontier N ↔ (z : V2) ∈ Q) ∧
        (∀ z : D, j z ∉ frontier R) ∧
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((Dehn.squareRimLoop.map rim.continuous).map
            (ContinuousMap.inclusion hMF).continuous)) ≠ 1 := by
  exact sourceSlab_phase_frontier_disk_alternative e phi he hfront hAB

end PoincareConjecture.M76.HamiltonIntervalTorus
