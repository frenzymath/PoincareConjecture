import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal










set_option autoImplicit false

open Filter

namespace PoincareConjecture.M30




theorem exists_strictMono_nestedSubsequence_diagonal
    (s : ℕ → ℕ → ℕ) (hs : ∀ i, StrictMono (s i))
    (hstep : ∀ i n, ∃ k, n ≤ k ∧ s (i + 1) n = s i k) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i N, ∀ᶠ j : ℕ in atTop,
        ∃ k, N ≤ k ∧ σ j = s i k := by
  have hrows (i j : ℕ) (hij : i ≤ j) (n : ℕ) :
      ∃ k, n ≤ k ∧ s j n = s i k := by
    induction j, hij using Nat.le_induction generalizing n with
    | base => exact ⟨n, le_rfl, rfl⟩
    | succ j hij ih =>
      obtain ⟨k, hnk, hk⟩ := hstep j n
      obtain ⟨l, hkl, hl⟩ := ih k
      exact ⟨l, hnk.trans hkl, hk.trans hl⟩
  let σ : ℕ → ℕ := fun j => s (j + 1) j
  have hσ : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro j
    obtain ⟨k, hjk, hk⟩ := hstep (j + 1) (j + 1)
    change s (j + 1) j < s (j + 1 + 1) (j + 1)
    rw [hk]
    exact hs (j + 1) ((Nat.lt_succ_self j).trans_le hjk)
  refine ⟨σ, hσ, fun i N => ?_⟩
  filter_upwards [eventually_ge_atTop (max i N)] with j hj
  have hij : i ≤ j + 1 :=
    ((le_max_left i N).trans hj).trans (Nat.le_succ j)
  obtain ⟨k, hjk, hk⟩ := hrows i (j + 1) hij j
  exact ⟨k, ((le_max_right i N).trans hj).trans hjk, hk⟩

end PoincareConjecture.M30
