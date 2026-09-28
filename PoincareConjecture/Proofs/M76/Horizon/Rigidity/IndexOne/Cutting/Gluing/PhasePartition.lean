import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.SourceSlab
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.ComplementarySlabContraction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.ClopenIncompressibility

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem sourceSlab_complementary_partition (phi : C(H, H)) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < p) :
    sourceSlab phi a b ∪ sourceSlab phi b (a + p) = R ∧
    sourceSlab phi a b ∩ sourceSlab phi b (a + p) =
      sourceSurface phi (a : C) ∪ sourceSurface phi (b : C) := by
  let q : C(R, C) := (sourcePhase phi).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  have hc := AddCircle.compl_interior_closedIntervalArc p ha hab hb
  have hf := AddCircle.frontier_closedIntervalArc p ha hab.le hb
  have hclosed := (AddCircle.isCompact_closedIntervalArc p a b).isClosed
  constructor
  · apply Subset.antisymm
    · exact union_subset (sourceSlab_subset phi a b) (sourceSlab_subset phi b (a + p))
    · intro x hx
      let x' : R := ⟨x, hx⟩
      by_cases hq : q x' ∈ interior (AddCircle.closedIntervalArc p a b)
      · exact Or.inl ((mem_sourceSlab_iff phi a b x').mpr (interior_subset hq))
      · exact Or.inr ((mem_sourceSlab_iff phi b (a + p) x').mpr (hc ▸ hq))
  · ext x
    constructor
    · intro hx
      let x' : R := ⟨x, sourceSlab_subset phi a b hx.1⟩
      have hq := (mem_sourceSlab_iff phi a b x').mp hx.1
      have hqc := (mem_sourceSlab_iff phi b (a + p) x').mp hx.2
      have hqf : q x' ∈ frontier (AddCircle.closedIntervalArc p a b) := by
        rw [frontier, hclosed.closure_eq]
        exact ⟨hq, show q x' ∈ (interior (AddCircle.closedIntervalArc p a b))ᶜ from
          hc.symm ▸ hqc⟩
      rw [hf] at hqf
      rcases hqf with hqa | hqb
      · exact Or.inl ((mem_sourceSurface_iff phi (a : C) x').mpr hqa)
      · exact Or.inr ((mem_sourceSurface_iff phi (b : C) x').mpr hqb)
    · intro hx
      have hxR : x ∈ R := hx.elim (fun h => sourceSurface_subset phi (a : C) h)
        (fun h => sourceSurface_subset phi (b : C) h)
      let x' : R := ⟨x, hxR⟩
      have hqf : q x' ∈ frontier (AddCircle.closedIntervalArc p a b) := by
        rw [hf]
        rcases hx with hx | hx
        · exact Or.inl ((mem_sourceSurface_iff phi (a : C) x').mp hx)
        · exact Or.inr ((mem_sourceSurface_iff phi (b : C) x').mp hx)
      rw [frontier, hclosed.closure_eq] at hqf
      exact ⟨(mem_sourceSlab_iff phi a b x').mpr hqf.1,
        (mem_sourceSlab_iff phi b (a + p) x').mpr (hc ▸ hqf.2)⟩

theorem sourceSurface_disjoint_of_ordered_phases (phi : C(H, H)) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < p) :
    Disjoint (sourceSurface phi (a : C)) (sourceSurface phi (b : C)) := by
  apply disjoint_left.mpr
  intro x hxA hxB
  let x' : R := ⟨x, sourceSurface_subset phi (a : C) hxA⟩
  have heq : (a : C) = (b : C) :=
    ((mem_sourceSurface_iff phi (a : C) x').mp hxA).symm.trans
      ((mem_sourceSurface_iff phi (b : C) x').mp hxB)
  have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
  have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
  exact (ne_of_lt hab) ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp heq)

theorem sourceSurface_union_pi1_injective (phi : C(H, H)) {a b : ℝ} {N : Set X}
    (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hA : IsClosed (sourceSurface phi (a : C)))
    (hB : IsClosed (sourceSurface phi (b : C)))
    (hAN : sourceSurface phi (a : C) ⊆ N)
    (hBN : sourceSurface phi (b : C) ⊆ N)
    (hpiA : ∀ x : sourceSurface phi (a : C),
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hAN) x))
    (hpiB : ∀ x : sourceSurface phi (b : C),
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hBN) x))
    (x : ↥(sourceSurface phi (a : C) ∪ sourceSurface phi (b : C))) :
    Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (union_subset hAN hBN)) x) := by
  exact FundamentalGroup.inclusion_injective_of_disjoint_closed_union hA hB
    (sourceSurface_disjoint_of_ordered_phases phi ha hab hb) rfl
    (union_subset hAN hBN) (fun _ => hpiA) (fun _ => hpiB) x

end PoincareConjecture.M76.HamiltonIntervalTorus
