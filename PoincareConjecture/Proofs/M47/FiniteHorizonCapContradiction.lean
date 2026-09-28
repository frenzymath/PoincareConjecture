import PoincareConjecture.Proofs.M47.TerminalCommonIntervalHorizon

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem terminalCommonInterval_slab_fails_above_horizon
    {V : GeneralizedBlowupSequence.{u}} {T : ℝ} (hT : 0 < T)
    (habove : terminalCommonIntervalHorizon V < ENNReal.ofReal T) :
    ¬ TerminalCommonIntervalSlab V T := by
  intro hslab
  have hmem : ENNReal.ofReal T ∈ TerminalCommonIntervalHorizons V := by
    intro U hU hUT
    exact terminalCommonInterval_slab_mono hslab
      ((ENNReal.ofReal_lt_ofReal_iff hT).mp hUT).le
  exact (not_lt_of_ge (le_sSup hmem)) habove

theorem finiteHorizon_neighborhood_fails
    {V : GeneralizedBlowupSequence.{u}} (Nbhd : ℕ → ℝ → ℝ → Prop)
    (thm11_8 : ∀ t : ℝ, 0 < t →
      (∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, Nbhd k A t) →
      ∀ T : ℝ, 0 < T → T < t → TerminalCommonIntervalSlab V T)
    {t : ℝ} (ht : 0 < t)
    (hT : terminalCommonIntervalHorizon V < ENNReal.ofReal t) :
    ∃ A : ℝ, 0 < A ∧ ∃ᶠ k in atTop, ¬ Nbhd k A t := by
  by_contra hnone
  push Not at hnone
  have hall : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, Nbhd k A t := by
    intro A hA
    exact hnone A hA
  have hreal : (terminalCommonIntervalHorizon V).toReal < t :=
    ENNReal.toReal_lt_of_lt_ofReal hT
  let T : ℝ := (terminalCommonIntervalHorizon V).toReal / 2 + t / 2
  have hTpos : 0 < T := by
    dsimp [T]
    have hnonneg : 0 ≤ (terminalCommonIntervalHorizon V).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hTlt : T < t := by
    dsimp [T]
    linarith
  have habove : terminalCommonIntervalHorizon V < ENNReal.ofReal T := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hT)).mpr
    dsimp [T]
    linarith
  exact terminalCommonInterval_slab_fails_above_horizon hTpos habove
    (thm11_8 t ht hall T hTpos hTlt)

theorem finiteHorizon_cap_contact_of_failed_neighborhood
    {Nbhd Contact : ℕ → ℝ → ℝ → Prop} {t : ℝ}
    (failure : ∃ A : ℝ, 0 < A ∧ ∃ᶠ k in atTop, ¬ Nbhd k A t)
    (cap_contact : ∀ A : ℝ, 0 < A →
      ∀ᶠ k in atTop, ¬ Nbhd k A t → Contact k A t) :
    ∃ A : ℝ, 0 < A ∧ ∃ᶠ k in atTop, Contact k A t := by
  obtain ⟨A, hA, hfail⟩ := failure
  refine ⟨A, hA, ?_⟩
  exact (hfail.and_eventually (cap_contact A hA)).mono
    (fun k hk => hk.2 hk.1)

theorem finiteHorizon_cap_persistence_contradiction
    {Contact LineBound Canonical : ℕ → ℝ → Prop}
    (hbad : ∀ k A, ¬ Canonical k A)
    (cap : ∃ A : ℝ, 0 < A ∧ ∃ᶠ k in atTop, Contact k A)
    (line_bound : ∀ A : ℝ, 0 < A →
      ∀ᶠ k in atTop, Contact k A → LineBound k A)
    (cap_persistence : ∀ A : ℝ, 0 < A →
      ∀ᶠ k in atTop, Contact k A → LineBound k A → Canonical k A) :
    False := by
  obtain ⟨A, hA, hcontact⟩ := cap
  have hline := line_bound A hA
  have hpersist := cap_persistence A hA
  have hcanonical : ∀ᶠ k in atTop, Contact k A → Canonical k A := by
    filter_upwards [hline, hpersist] with k hk_line hk_persist hk_contact
    exact hk_persist hk_contact (hk_line hk_contact)
  obtain ⟨k, hk_contact, hk_canonical⟩ :=
    (hcontact.and_eventually hcanonical).exists
  exact hbad k A (hk_canonical hk_contact)

end PoincareConjecture.M47
