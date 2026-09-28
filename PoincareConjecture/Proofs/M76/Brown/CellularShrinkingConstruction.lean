import PoincareConjecture.Proofs.M76.Brown.CellularShrinking
import PoincareConjecture.Proofs.M76.Brown.SupportedCellShrinking
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Homeomorph

variable {X E : Type*} [MetricSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem exists_collapse_of_nested_ballPairs
    (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n))
    (hnest : ∀ n, K (n + 1) ⊆ interior (K n))
    (hpair : ∀ n, IsUnitBallPair E (K n) (frontier (K n))) :
    ∃ f : C(X, X), Function.Surjective f ∧
      (∀ x y, f x = f y ↔ x = y ∨ (x ∈ ⋂ n, K n) ∧ (y ∈ ⋂ n, K n)) ∧
      EqOn f id (interior (K 0))ᶜ := by
  classical
  have hanti : Antitone K := antitone_nat_of_succ_le fun n =>
    (hnest n).trans interior_subset
  have hpos (n : ℕ) : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  choose shrink hfix hsmall using fun (n : ℕ) (H : X ≃ₜ X) =>
    (hpair n).exists_supported_shrinking (hK n).isClosed (hK (n + 1))
      (hnest n) H H.continuous.continuousOn (hpos n)
  let H : ℕ → X ≃ₜ X := Nat.rec (Homeomorph.refl X)
    (fun n Hn => (shrink n Hn).trans Hn)
  have hHsucc (n : ℕ) (x : X) :
      H (n + 1) x = H n (shrink n (H n) x) := rfl
  have hHfix (n : ℕ) (x : X) (hx : x ∉ interior (K 0)) : H n x = x := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [hHsucc, hfix n (H n) (fun h => hx (interior_mono (hanti (Nat.zero_le n)) h))]
        exact ih
  have hstep (n : ℕ) : EqOn (H ((n + 1) + 1)) (H (n + 1)) (K (n + 1))ᶜ := by
    intro x hx
    rw [hHsucc, hfix (n + 1) (H (n + 1)) (fun h => hx (interior_subset h))]
    rfl
  have hbound (n : ℕ) (x : X) (hx : x ∈ K (n + 1))
      (y : X) (hy : y ∈ K (n + 1)) :
      dist (H (n + 1) x) (H (n + 1) y) ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
    rw [hHsucc, hHsucc]
    exact (hsmall n (H n) x hx y hy).le
  obtain ⟨f, _, hf, hfib, hfixed⟩ := exists_collapse_of_nested_shrinking
    (fun n => K (n + 1)) (fun n => (hK (n + 1)).isClosed)
    (fun n m hnm => hanti (Nat.add_le_add_right hnm 1))
    (fun n => H (n + 1)) hstep (fun n => (1 : ℝ) / ((n : ℝ) + 1))
    (fun n => (hpos n).le) tendsto_one_div_add_atTop_nhds_zero_nat hbound
  have hinter : (⋂ n, K (n + 1)) = ⋂ n, K n := by
    ext x
    simp only [mem_iInter]
    constructor
    · intro hx n
      exact hanti (Nat.le_succ n) (hx n)
    · intro hx n
      exact hx (n + 1)
  refine ⟨f, hf, ?_, ?_⟩
  · simpa only [hinter] using hfib
  · intro x hx
    exact hfixed x (fun n => hHfix (n + 1) x hx)

end Homeomorph
