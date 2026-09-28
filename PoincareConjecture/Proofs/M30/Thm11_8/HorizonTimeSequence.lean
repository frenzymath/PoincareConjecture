import PoincareConjecture.Definitions.Ch11.BlowupLimits
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas













set_option autoImplicit false

open Set Filter
open scoped ENNReal Topology

namespace PoincareConjecture.M30




theorem exists_strictMono_backward_time_exhaustion
    {T0 : ℝ≥0∞} (hT0 : 0 < T0) :
    ∃ T : ℕ → ℝ, StrictMono T ∧
      (∀ k, 0 < T k ∧ ENNReal.ofReal (T k) < T0) ∧
      (∀ r : ℝ, ENNReal.ofReal r < T0 → ∀ᶠ k : ℕ in atTop, r < T k) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ blowupBackwardInterval T0 →
        ∀ᶠ k : ℕ in atTop, K ⊆ Icc (-(T k)) 0 := by
  obtain ⟨U, hU, hmem, hlim⟩ := exists_seq_strictMono_tendsto' hT0
  have hfinite (k : ℕ) : U k ≠ ⊤ := ((hmem k).2.trans_le le_top).ne
  let T (k : ℕ) : ℝ := (U k).toReal
  have hpos (k : ℕ) : 0 < T k := ENNReal.toReal_pos (hmem k).1.ne' (hfinite k)
  have hvalue (k : ℕ) : ENNReal.ofReal (T k) = U k :=
    ENNReal.ofReal_toReal (hfinite k)
  have hcofinal (r : ℝ) (hr : ENNReal.ofReal r < T0) :
      ∀ᶠ k : ℕ in atTop, r < T k := by
    filter_upwards [hlim.eventually (Ioi_mem_nhds hr)] with k hk
    rw [← hvalue k] at hk
    exact (ENNReal.ofReal_lt_ofReal_iff (hpos k)).mp hk
  refine ⟨T, ?_, ?_, hcofinal, ?_⟩
  · intro i j hij
    exact (ENNReal.toReal_lt_toReal (hfinite i) (hfinite j)).mpr (hU hij)
  · intro k
    exact ⟨hpos k, (hvalue k).trans_lt (hmem k).2⟩
  · intro K hK hKJ
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact Eventually.of_forall fun _ => empty_subset _
    obtain ⟨a, haK, ha⟩ := hK.exists_isLeast hKne
    filter_upwards [hcofinal (-a) (hKJ haK).2] with k hk t ht
    exact ⟨(by linarith [ha ht]), (hKJ ht).1⟩

end PoincareConjecture.M30
