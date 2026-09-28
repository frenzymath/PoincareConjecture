import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push

set_option autoImplicit false

open Set

namespace Metric

theorem totallyBounded_univ_of_finite_pair_collision
    {Y : Type*} [PseudoMetricSpace Y]
    (hpacking : ∀ epsilon : ℝ, 0 < epsilon → ∃ K : ℕ,
      ∀ p : Fin (K + 1) → Y, ∃ i j : Fin (K + 1), i ≠ j ∧
        dist (p i) (p j) < epsilon) :
    TotallyBounded (univ : Set Y) := by
  classical
  apply totallyBounded_iff.mpr
  intro epsilon hepsilon
  obtain ⟨K, hK⟩ := hpacking epsilon hepsilon
  by_contra hcover
  have hnew {n : ℕ} (p : Fin n → Y) :
      ∃ x : Y, ∀ i : Fin n, epsilon ≤ dist x (p i) := by
    by_contra! hbad
    apply hcover
    refine ⟨range p, finite_range p, ?_⟩
    intro x _hx
    obtain ⟨i, hi⟩ := hbad x
    exact mem_iUnion₂.mpr ⟨p i, mem_range_self i, hi⟩
  have hfamily : ∀ n : ℕ, ∃ p : Fin n → Y,
      ∀ i j : Fin n, i ≠ j → epsilon ≤ dist (p i) (p j) := by
    intro n
    induction n with
    | zero =>
      exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨x, hx⟩ := hnew p
      refine ⟨Fin.cases x p, ?_⟩
      intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa using hx j
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa [dist_comm] using hx i
        | succ j =>
          have hne : i ≠ j := fun h => hij (congrArg Fin.succ h)
          simpa using hp i j hne
  obtain ⟨p, hp⟩ := hfamily (K + 1)
  obtain ⟨i, j, hij, hclose⟩ := hK p
  exact (not_le_of_gt hclose) (hp i j hij)

end Metric

namespace UniformSpace.Completion

theorem compactSpace_of_totallyBounded_univ
    {Y : Type*} [PseudoMetricSpace Y] (hY : TotallyBounded (univ : Set Y)) :
    CompactSpace (Completion Y) := by
  have hclosure := (hY.image (uniformContinuous_coe Y)).closure
  have hfull : closure (((↑) : Y → Completion Y) '' univ) = univ := by
    simpa only [image_univ] using (denseRange_coe (α := Y)).closure_range
  rw [hfull] at hclosure
  exact ⟨hclosure.isCompact_of_isClosed isClosed_univ⟩

end UniformSpace.Completion
