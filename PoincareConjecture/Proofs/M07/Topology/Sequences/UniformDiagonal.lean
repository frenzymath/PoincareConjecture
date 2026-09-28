import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic









namespace Poincare

open Filter Set
open scoped Topology




theorem exists_strictMono_tendstoUniformlyOn_diagonal
    {X Y : ℕ → Type*} [∀ i, PseudoMetricSpace (Y i)]
    (f : ∀ i, ℕ → ℕ → X i → Y i) (g : ∀ i, X i → Y i)
    (K : ∀ i, ℕ → Set (X i)) (hK : ∀ i, Monotone (K i))
    (hconv : ∀ j i, i ≤ j → TendstoUniformlyOn (f i j) (g i) atTop (K i j))
    {P : ℕ → ℕ → Prop} (hP : ∀ j, ∀ᶠ k in atTop, P j k) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ j, P j (σ j)) ∧
      ∀ i l, TendstoUniformlyOn (fun j => f i j (σ j)) (g i) atTop (K i l) := by
  have hrow (j : ℕ) : ∀ᶠ k in atTop,
      P j k ∧ ∀ i ≤ j, ∀ x ∈ K i j,
        dist (g i x) (f i j k x) < 1 / ((j : ℝ) + 1) := by
    have htests : ∀ᶠ k in atTop, ∀ i ∈ Finset.range (j + 1), ∀ x ∈ K i j,
        dist (g i x) (f i j k x) < 1 / ((j : ℝ) + 1) := by
      apply (eventually_all_finset _).mpr
      intro i hi
      exact (Metric.tendstoUniformlyOn_iff.mp
        (hconv j i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) _ (by positivity)
    filter_upwards [hP j, htests] with k hk htest
    exact ⟨hk, fun i hi => htest i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))⟩
  obtain ⟨σ, hσ, hselect⟩ := exists_strictMono_forall_le_of_eventually hrow
  refine ⟨σ, hσ, fun j => (hselect j j le_rfl).1, fun i l => ?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop i, eventually_ge_atTop l, hsmall] with j hij hlj hj
  intro x hx
  exact ((hselect j j le_rfl).2 i hij x (hK i hlj hx)).trans hj

end Poincare
