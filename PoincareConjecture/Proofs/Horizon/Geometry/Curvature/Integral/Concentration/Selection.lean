import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter

namespace Poincare.CurvatureIntegral

theorem exists_strictMono_above_thresholds_family
    (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hlarge : ∀ k, ∀ C : ℝ, ∃ j : ℕ, C < a k j) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ k, b k < a k (phi k) := by
  classical
  have hnext (i k : ℕ) : ∃ j : ℕ, i < j ∧ b k < a k j := by
    obtain ⟨C, hC⟩ := ((Set.finite_Iic i).image (a k)).bddAbove
    obtain ⟨j, hj⟩ := hlarge k (max C (b k))
    refine ⟨j, ?_, (le_max_right _ _).trans_lt hj⟩
    by_contra hji
    have := hC ⟨j, not_lt.mp hji, rfl⟩
    exact (not_le_of_gt ((le_max_left _ _).trans_lt hj)) this
  choose next hindex hvalue using hnext
  let phi : ℕ → ℕ := fun k => Nat.rec (next 0 0) (fun i j => next j (i + 1)) k
  refine ⟨phi, strictMono_nat_of_lt_succ (fun k => hindex (phi k) (k + 1)), ?_⟩
  intro k
  cases k with
  | zero => exact hvalue 0 0
  | succ k => exact hvalue (phi k) (k + 1)

theorem exists_strictMono_above_thresholds
    (a b : ℕ → ℝ) (hlarge : ∀ C : ℝ, ∃ j : ℕ, C < a j) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ k, b k < a (phi k) :=
  exists_strictMono_above_thresholds_family (fun _ => a) b (fun _ => hlarge)

end Poincare.CurvatureIntegral
