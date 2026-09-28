import PoincareConjecture.Proofs.M47.TerminalCommonIntervalHorizon
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem terminalCommonInterval_cofinal_times {H : ℝ≥0∞} (hH : 0 < H) :
    ∃ T buffered : ℕ → ℝ, StrictMono T ∧ StrictMono buffered ∧
      (∀ j, 0 < T j ∧ T j < buffered j ∧ ENNReal.ofReal (buffered j) < H) ∧
      (∀ t : ℝ, 0 < t → ENNReal.ofReal t < H → ∃ j, t < T j) := by
  obtain ⟨f, hf, hmem, hlim⟩ := exists_seq_strictMono_tendsto' hH
  have hfinite (j : ℕ) : f j ≠ ⊤ := ((hmem j).2.trans_le le_top).ne
  let T : ℕ → ℝ := fun j => (f (2 * j)).toReal
  let buffered : ℕ → ℝ := fun j => (f (2 * j + 1)).toReal
  refine ⟨T, buffered, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (ENNReal.toReal_lt_toReal (hfinite _) (hfinite _)).mpr
      (hf (by omega : 2 * i < 2 * j))
  · intro i j hij
    exact (ENNReal.toReal_lt_toReal (hfinite _) (hfinite _)).mpr
      (hf (by omega : 2 * i + 1 < 2 * j + 1))
  · intro j
    refine ⟨ENNReal.toReal_pos (hmem _).1.ne' (hfinite _),
      (ENNReal.toReal_lt_toReal (hfinite _) (hfinite _)).mpr (hf (by omega)), ?_⟩
    dsimp only [buffered]
    rw [ENNReal.ofReal_toReal (hfinite _)]
    exact (hmem _).2
  · intro t ht htH
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_nhds htH)).exists
    refine ⟨n, ?_⟩
    have hlt : ENNReal.ofReal t < f (2 * n) := hn.trans_le (hf.monotone (by omega))
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hfinite _)).mp hlt

theorem terminalCommonInterval_row_bounds
    (V : GeneralizedBlowupSequence.{u}) (T : ℕ → ℝ)
    (hT : ∀ j, 0 < T j ∧ ENNReal.ofReal (T j) < terminalCommonIntervalHorizon V) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ j : ℕ, ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k in atTop, Nonempty (ControlledBlowupCylinder V k A (T j) (B j) eta) := by
  choose B hB hc using fun j => terminalCommonInterval_horizon_mem V (T j) (hT j).1 (hT j).2
  exact ⟨B, hB, hc⟩

theorem terminalCommonInterval_diagonal_cylinders
    (V : GeneralizedBlowupSequence.{u}) (T B : ℕ → ℝ)
    (hc : ∀ j : ℕ, ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ k in atTop, Nonempty (ControlledBlowupCylinder V k A (T j) (B j) eta)) :
    ∃ beta : ℕ → ℕ, StrictMono beta ∧ ∀ n j : ℕ, j ≤ n →
      Nonempty (ControlledBlowupCylinder V (beta n) (n + 1) (T j) (B j) (1 / (n + 1))) := by
  have hrow (n : ℕ) : ∀ᶠ k in atTop, ∀ j ∈ Finset.range (n + 1),
      Nonempty (ControlledBlowupCylinder V k (n + 1) (T j) (B j) (1 / (n + 1))) := by
    apply (eventually_all_finset _).mpr
    intro j _hj
    exact hc j (n + 1) (by positivity) (1 / (n + 1)) (by positivity)
  obtain ⟨beta, hbeta, hb⟩ := Poincare.exists_strictMono_forall_le_of_eventually hrow
  exact ⟨beta, hbeta, fun n j hj => hb n n le_rfl j (Finset.mem_range.mpr (by omega))⟩

theorem terminalCommonInterval_buffered_diagonal
    (V : GeneralizedBlowupSequence.{u}) (hH : 0 < terminalCommonIntervalHorizon V) :
    ∃ T buffered B : ℕ → ℝ, StrictMono T ∧ StrictMono buffered ∧
      (∀ j, 0 < T j ∧ T j < buffered j ∧
        ENNReal.ofReal (buffered j) < terminalCommonIntervalHorizon V) ∧
      (∀ t : ℝ, 0 < t → ENNReal.ofReal t < terminalCommonIntervalHorizon V →
        ∃ j, t < T j) ∧
      (∀ j, 0 ≤ B j) ∧ ∃ beta : ℕ → ℕ, StrictMono beta ∧ ∀ n j : ℕ, j ≤ n →
        Nonempty (ControlledBlowupCylinder V (beta n) (n + 1)
          (buffered j) (B j) (1 / (n + 1))) := by
  obtain ⟨T, buffered, hT, hb, hbuffer, hcofinal⟩ := terminalCommonInterval_cofinal_times hH
  obtain ⟨B, hB, hc⟩ := terminalCommonInterval_row_bounds V buffered
    (fun j => ⟨(hbuffer j).1.trans (hbuffer j).2.1, (hbuffer j).2.2⟩)
  obtain ⟨beta, hbeta, hd⟩ := terminalCommonInterval_diagonal_cylinders V buffered B hc
  exact ⟨T, buffered, B, hT, hb, hbuffer, hcofinal, hB, beta, hbeta, hd⟩

end PoincareConjecture.M47
