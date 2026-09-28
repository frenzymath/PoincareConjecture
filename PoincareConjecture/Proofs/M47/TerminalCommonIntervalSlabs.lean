import PoincareConjecture.Proofs.M47.TerminalCommonIntervalDecision

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M47

def TerminalCommonIntervalSlab (V : GeneralizedBlowupSequence.{u}) (T : ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
    ∀ᶠ k in atTop, Nonempty (ControlledBlowupCylinder V k A T B eta)

def TerminalCommonIntervalHorizons (V : GeneralizedBlowupSequence.{u}) : Set ℝ≥0∞ :=
  {H | ∀ T : ℝ, 0 < T → ENNReal.ofReal T < H → TerminalCommonIntervalSlab V T}

theorem terminalCommonInterval_slab_mono
    {V : GeneralizedBlowupSequence.{u}} {T T' : ℝ}
    (h : TerminalCommonIntervalSlab V T) (hT : T' ≤ T) :
    TerminalCommonIntervalSlab V T' := by
  obtain ⟨B, hB, hc⟩ := h
  refine ⟨B, hB, fun A hA eta heta => ?_⟩
  filter_upwards [hc A hA eta heta] with k hk
  exact hk.map (fun e => terminalCommonInterval_restrict e le_rfl hT le_rfl le_rfl)

theorem terminalCommonInterval_slab_reindex
    {V : GeneralizedBlowupSequence.{u}} {T : ℝ}
    (h : TerminalCommonIntervalSlab V T) {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) :
    TerminalCommonIntervalSlab (terminalCommonInterval_reindex V sigma hsigma) T := by
  obtain ⟨B, hB, hc⟩ := h
  refine ⟨B, hB, fun A hA eta heta => ?_⟩
  filter_upwards [hsigma.tendsto_atTop.eventually (hc A hA eta heta)] with k hk
  exact terminalCommonInterval_reindex_cylinder_iff.mpr hk

theorem terminalCommonInterval_slab_iff_tests
    (V : GeneralizedBlowupSequence.{u}) (T : ℝ) :
    TerminalCommonIntervalSlab V T ↔
      ∃ b : ℕ, ∀ a m : ℕ, ∀ᶠ k in atTop,
        Nonempty (ControlledBlowupCylinder V k (a + 1) T b (1 / (m + 1))) := by
  constructor
  · rintro ⟨B, _hB, hc⟩
    obtain ⟨b, hb⟩ := exists_nat_ge B
    refine ⟨b, fun a m => ?_⟩
    filter_upwards [hc (a + 1) (by positivity) (1 / (m + 1)) (by positivity)] with k hk
    exact hk.map (fun e => terminalCommonInterval_restrict e le_rfl le_rfl hb le_rfl)
  · rintro ⟨b, hc⟩
    refine ⟨b, Nat.cast_nonneg b, fun A _hA eta heta => ?_⟩
    obtain ⟨a, ha⟩ := exists_nat_ge A
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt heta
    filter_upwards [hc a m] with k hk
    exact hk.map (fun e => terminalCommonInterval_restrict e
      (by linarith : A ≤ (a : ℝ) + 1) le_rfl le_rfl hm.le)

theorem terminalCommonInterval_rational_slab_reflect
    {V : GeneralizedBlowupSequence.{u}} (hdec : TerminalCommonIntervalDecided V)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) (q : ℚ)
    (h : TerminalCommonIntervalSlab (terminalCommonInterval_reindex V sigma hsigma) q) :
    TerminalCommonIntervalSlab V q := by
  obtain ⟨b, hb⟩ := (terminalCommonInterval_slab_iff_tests _ _).mp h
  apply (terminalCommonInterval_slab_iff_tests _ _).mpr
  refine ⟨b, fun a m => ?_⟩
  rcases hdec q b a m with hyes | hno
  · exact hyes
  · have htrue : ∀ᶠ k in atTop,
        Nonempty (ControlledBlowupCylinder V (sigma k) (a + 1) q b (1 / (m + 1))) :=
      (hb a m).mono (fun _ hk => terminalCommonInterval_reindex_cylinder_iff.mp hk)
    obtain ⟨k, hk, hn⟩ := (htrue.and (hsigma.tendsto_atTop.eventually hno)).exists
    exact (hn hk).elim

theorem terminalCommonInterval_rational_buffer {T : ℝ} {H : ℝ≥0∞}
    (hT : 0 < T) (hH : ENNReal.ofReal T < H) :
    ∃ q : ℚ, T < (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < H := by
  by_cases htop : H = ⊤
  · obtain ⟨q, hq, _⟩ := exists_rat_btwn (show T < T + 1 by linarith)
    exact ⟨q, hq, htop ▸ ENNReal.ofReal_lt_top⟩
  · have hreal : T < H.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hT.le htop).mp hH
    obtain ⟨q, hq, hqH⟩ := exists_rat_btwn hreal
    exact ⟨q, hq, (ENNReal.ofReal_lt_iff_lt_toReal (hT.trans hq).le htop).mpr hqH⟩

theorem terminalCommonInterval_horizons_reindex
    {V : GeneralizedBlowupSequence.{u}} (hdec : TerminalCommonIntervalDecided V)
    {sigma : ℕ → ℕ} (hsigma : StrictMono sigma) :
    TerminalCommonIntervalHorizons (terminalCommonInterval_reindex V sigma hsigma) =
      TerminalCommonIntervalHorizons V := by
  ext H
  constructor
  · intro h T hT hTH
    obtain ⟨q, hq, hqH⟩ := terminalCommonInterval_rational_buffer hT hTH
    exact terminalCommonInterval_slab_mono
      (terminalCommonInterval_rational_slab_reflect hdec hsigma q
        (h q (hT.trans hq) hqH)) hq.le
  · intro h T hT hTH
    exact terminalCommonInterval_slab_reindex (h T hT hTH) hsigma

end PoincareConjecture.M47
