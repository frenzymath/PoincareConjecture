import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourcePhaseSets
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.PhaseArc

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem sourceSlab_isCompact (phi : C(H, H)) (a b : ℝ) :
    IsCompact (sourceSlab phi a b) := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let : CompactSpace R := isCompact_iff_compactSpace.mp
    (isCompact_latticeHandleDomain (Fin 1) (Fin 2) L)
  let q : C(R, C) := (sourcePhase phi).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  exact ((AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage q.continuous).isCompact.image
    continuous_subtype_val

theorem sourceSlab_interior_phase_iff
    (phi : C(H, H)) {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    {x : X} (hx : x ∈ interior R) :
    x ∈ interior (sourceSlab phi a b) ↔
      ambientSourcePhase phi x ∈ interior (AddCircle.closedIntervalArc p a b) := by
  have hxR : x ∈ R := interior_subset hx
  have hxB : x ∉ frontier R := fun h => disjoint_left.mp disjoint_interior_frontier hx h
  have hmem : x ∈ sourceSlab phi a b ↔
      ambientSourcePhase phi x ∈ AddCircle.closedIntervalArc p a b := by
    rw [sourceSlab_eq_inter_phase]
    exact and_iff_right hxR
  have hf : x ∈ frontier (sourceSlab phi a b) ↔
      ambientSourcePhase phi x ∈ frontier (AddCircle.closedIntervalArc p a b) := by
    rw [hfront, AddCircle.frontier_closedIntervalArc_shifted p ha hab.le hb,
      sourceSurface_eq_inter_phase, sourceSurface_eq_inter_phase]
    simp only [mem_union, mem_inter_iff, hxB, and_false, false_or, mem_preimage,
      hxR, true_and, mem_singleton_iff, mem_insert_iff]
  rw [← self_sdiff_frontier (sourceSlab phi a b),
    ← self_sdiff_frontier (AddCircle.closedIntervalArc p a b)]
  exact and_congr hmem (not_congr hf)

theorem complementary_sourceSlab_agrees_exterior
    (phi : C(H, H)) {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C))) :
    ∀ x ∈ interior R, x ∈ sourceSlab phi b (a + p) ↔ x ∈ (interior (sourceSlab phi a b))ᶜ := by
  intro x hx
  rw [sourceSlab_eq_inter_phase, ← compl_interior_shifted_phase_arc p ha hab hb]
  change (x ∈ R ∧ ambientSourcePhase phi x ∉ interior (AddCircle.closedIntervalArc p a b)) ↔ _
  rw [and_iff_right (interior_subset hx)]
  exact (not_congr (sourceSlab_interior_phase_iff phi ha hab hb hfront hx)).symm

end PoincareConjecture.M76.HamiltonIntervalTorus
