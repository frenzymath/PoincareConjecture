import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalRadius

set_option autoImplicit false

open Set Filter

namespace PoincareConjecture.M28.tube

universe u

theorem critical_witnesses_cofinal_below
    {X : ℕ → Type u} {d q : ∀ k, X k → ℝ} {A : ℝ}
    (hinterior : ∀ r < A, eventuallyRadiusBound d q r)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (x : ∀ j, X (φ j))
    (hx : ∀ j, d (φ j) (x j) < A + 1 / ((j : ℝ) + 1) ∧
      (j : ℝ) < q (φ j) (x j)) :
    ∀ n : ℕ, ∃ j : ℕ,
      A - 1 / ((n : ℝ) + 1) < d (φ j) (x j) := by
  intro n
  by_contra hnot
  push Not at hnot
  let r : ℝ := A - 1 / (2 * ((n : ℝ) + 1))
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hr : r < A := by
    dsimp [r]
    have : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    linarith
  obtain ⟨K, hK⟩ := hinterior r hr
  have hKφ : ∀ᶠ j : ℕ in atTop,
      ∀ y : X (φ j), d (φ j) y < r → q (φ j) y ≤ K :=
    hφ.tendsto_atTop.eventually hK
  have hJ : ∀ᶠ j : ℕ in atTop, K < (j : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop K)
  obtain ⟨j, hjK, hj⟩ := (hKφ.and hJ).exists
  have hdle : d (φ j) (x j) ≤ A - 1 / ((n : ℝ) + 1) := hnot j
  have hdr : d (φ j) (x j) < r := by
    dsimp [r]
    have hden : (n : ℝ) + 1 < 2 * ((n : ℝ) + 1) := by linarith
    have hhalf : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) :=
      one_div_lt_one_div_of_lt hn hden
    linarith
  have hq := hjK (x j) hdr
  exact (not_lt_of_ge hq) (hj.trans (hx j).2)

end PoincareConjecture.M28.tube
