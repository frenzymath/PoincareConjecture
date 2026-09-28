import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCompactMaps









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology NNReal

universe u v

namespace PoincareConjecture.M47



theorem terminalCommonInterval_captured_rows
    {M : Type u} {N : Type v} [MetricSpace M] [MetricSpace N]
    (K : ℕ → Set M) (L : ℕ → Set N) (q : N) (hq : ∀ j, q ∈ L j)
    (C : ℝ≥0) (T : ℕ → M → N)
    (hT : ∀ j, ∀ᶠ n in atTop, MapsTo (T n) (K j) (L j) ∧
      LipschitzOnWith C (T n) (K j)) :
    ∃ F : ∀ j, ℕ → C(K j, L j),
      (∀ j n, LipschitzWith C (F j n)) ∧
      ∀ j, ∀ᶠ n in atTop, ∀ x : K j, (F j n x).val = T n x := by
  classical
  let good (j n : ℕ) := MapsTo (T n) (K j) (L j) ∧ LipschitzOnWith C (T n) (K j)
  have hgood (j n : ℕ) (hg : good j n) :
      LipschitzWith C (fun x : K j => (⟨T n x, hg.1 x.property⟩ : L j)) :=
    fun x y => hg.2 x.property y.property
  let F (j n : ℕ) : C(K j, L j) := if hg : good j n then
    ⟨fun x => ⟨T n x, hg.1 x.property⟩, (hgood j n hg).continuous⟩
    else ContinuousMap.const (K j) ⟨q, hq j⟩
  refine ⟨F, ?_, ?_⟩
  · intro j n
    dsimp only [F]
    split_ifs with hg
    · exact hgood j n hg
    · intro x y
      simp
  · intro j
    filter_upwards [hT j] with n hn x
    dsimp [F]
    rw [dif_pos hn]
    rfl

end PoincareConjecture.M47
