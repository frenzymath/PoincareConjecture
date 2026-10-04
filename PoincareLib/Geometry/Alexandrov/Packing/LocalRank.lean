import PoincareLib.Geometry.Alexandrov.Packing.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fin.SuccPred

/-!
# Local angular packing rank

The cardinalities of angular configurations on arbitrarily small common
spheres form a finite initial segment under a uniform angular packing bound.
Its largest element defines a local rank, whose global minimum is attained.
This finite-configuration invariant supports the bounded-integer argument of
Petrunin (2009), Sections 3.3 and 4.7, author manuscript pp. 6 and 14.
-/

set_option autoImplicit false

open Set

namespace Poincare.Alexandrov

/-- Angular configurations of cardinality `k` on arbitrarily small common
spheres about `p`. The indexed points are not required separately to differ. -/
def HasSmallAngleConfiguration {X : Type*} [MetricSpace X]
    (θ : ℝ) (p : X) (k : ℕ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ R : ℝ, 0 < R ∧ R < ρ ∧
    ∃ q : Fin k → X, (∀ i, dist p (q i) = R) ∧
      ∀ i l : Fin k, i ≠ l →
        θ < comparisonAngle (dist p (q i)) (dist p (q l)) (dist (q i) (q l))

/-- Largest local angular-configuration cardinality, with the natural-number
supremum convention when the cardinalities are unbounded. -/
noncomputable def localAnglePackingRank {X : Type*} [MetricSpace X]
    (θ : ℝ) (p : X) : ℕ := sSup {k | HasSmallAngleConfiguration θ p k}

/-- The minimum local angular packing rank, with value zero on the empty space. -/
noncomputable def minLocalAnglePackingRank (X : Type*) [MetricSpace X]
    (θ : ℝ) : ℕ := sInf (Set.range (localAnglePackingRank (X := X) θ))

theorem hasSmallAngleConfiguration_zero {X : Type*} [MetricSpace X] (θ : ℝ) (p : X) :
    HasSmallAngleConfiguration θ p 0 := by
  intro ρ hρ
  refine ⟨ρ / 2, half_pos hρ, half_lt_self hρ, Fin.elim0, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

theorem HasSmallAngleConfiguration.mono {X : Type*} [MetricSpace X]
    {θ : ℝ} {p : X} {k l : ℕ} (hk : HasSmallAngleConfiguration θ p k) (hlk : l ≤ k) :
    HasSmallAngleConfiguration θ p l := by
  intro ρ hρ
  obtain ⟨R, hR, hRρ, q, hq, hangle⟩ := hk ρ hρ
  refine ⟨R, hR, hRρ, q ∘ Fin.castLE hlk, fun i => hq _, ?_⟩
  intro i j hij
  exact hangle _ _ (fun heq => hij (Fin.castLE_injective hlk heq))

theorem HasSmallAngleConfiguration.le_packingBound
    {X : Type*} [MetricSpace X] {θ : ℝ} {N k : ℕ} {p : X}
    (hk : HasSmallAngleConfiguration θ p k)
    (hpack : ComparisonAnglePackingBound X θ N) : k ≤ N := by
  obtain ⟨R, hR, _, q, hq, hangle⟩ := hk 1 zero_lt_one
  apply hpack k p q ?_ hangle
  intro i heq
  have hz := hq i
  rw [heq, dist_self] at hz
  exact (ne_of_gt hR) hz.symm

/-- Under a packing bound the local rank is attained, bounded, and describes
exactly every locally realizable cardinality. -/
theorem localAnglePackingRank_spec
    {X : Type*} [MetricSpace X] {θ : ℝ} {N : ℕ}
    (hpack : ComparisonAnglePackingBound X θ N) (p : X) :
    HasSmallAngleConfiguration θ p (localAnglePackingRank θ p) ∧
      localAnglePackingRank θ p ≤ N ∧
      ∀ k : ℕ, HasSmallAngleConfiguration θ p k ↔ k ≤ localAnglePackingRank θ p := by
  have hnonempty : {k | HasSmallAngleConfiguration θ p k}.Nonempty :=
    ⟨0, hasSmallAngleConfiguration_zero θ p⟩
  have hbounded : BddAbove {k | HasSmallAngleConfiguration θ p k} :=
    ⟨N, fun _ hk => hk.le_packingBound hpack⟩
  have hattain : HasSmallAngleConfiguration θ p (localAnglePackingRank θ p) :=
    Nat.sSup_mem hnonempty hbounded
  refine ⟨hattain, hattain.le_packingBound hpack, ?_⟩
  intro k
  exact ⟨fun hk => le_csSup hbounded hk, fun hk => hattain.mono hk⟩

/-- A nonempty metric space has a point attaining the minimum local rank,
and this minimum obeys the same angular packing bound. -/
theorem minLocalAnglePackingRank_spec
    {X : Type*} [MetricSpace X] [Nonempty X] {θ : ℝ} {N : ℕ}
    (hpack : ComparisonAnglePackingBound X θ N) :
    (∃ p : X, localAnglePackingRank θ p = minLocalAnglePackingRank X θ) ∧
      (∀ p : X, minLocalAnglePackingRank X θ ≤ localAnglePackingRank θ p) ∧
      minLocalAnglePackingRank X θ ≤ N := by
  have hattain : ∃ p : X, localAnglePackingRank θ p = minLocalAnglePackingRank X θ :=
    Nat.sInf_mem (Set.range_nonempty (localAnglePackingRank (X := X) θ))
  have hle (p : X) : minLocalAnglePackingRank X θ ≤ localAnglePackingRank θ p :=
    Nat.sInf_le (Set.mem_range_self p)
  obtain ⟨p, hp⟩ := hattain
  refine ⟨⟨p, hp⟩, hle, ?_⟩
  rw [← hp]
  exact (localAnglePackingRank_spec hpack p).2.1

private theorem exists_nonincreasing_step_of_bounded
    (r : ℕ → ℕ) (N : ℕ) (hbound : ∀ j, r j ≤ N) :
    ∃ j : ℕ, j ≤ N ∧ r (j + 1) ≤ r j := by
  by_contra! hfail
  have hinc (j : ℕ) (hj : j ≤ N + 1) : j ≤ r j := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hprev := ih (by omega)
      have hstep := hfail j (by omega)
      omega
  have hlast := hinc (N + 1) le_rfl
  have hupper := hbound (N + 1)
  omega

/-- Uniformly bounded angular packing allows only finitely many successive
strict increases of the global minimum local rank. -/
theorem exists_nonincreasing_minLocalAnglePackingRank_step
    {X : ℕ → Type*} [∀ j, MetricSpace (X j)] [∀ j, Nonempty (X j)]
    {θ : ℝ} {N : ℕ} (hpack : ∀ j, ComparisonAnglePackingBound (X j) θ N) :
    ∃ j : ℕ, j ≤ N ∧
      minLocalAnglePackingRank (X (j + 1)) θ ≤ minLocalAnglePackingRank (X j) θ := by
  exact exists_nonincreasing_step_of_bounded
    (fun j => minLocalAnglePackingRank (X j) θ) N
    (fun j => (minLocalAnglePackingRank_spec (hpack j)).2.2)

end Poincare.Alexandrov
