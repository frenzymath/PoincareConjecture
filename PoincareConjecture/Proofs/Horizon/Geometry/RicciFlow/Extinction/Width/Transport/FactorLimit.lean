import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.EventWidthTransport

set_option autoImplicit false

namespace PoincareConjecture


theorem le_of_factor_sq_mul_forall_eta {v w : ℝ} (hw : 0 ≤ w)
    (h : ∀ eta : ℝ, 0 < eta → v ≤ (1 + eta) ^ 2 * w) :
    v ≤ w := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  by_cases hbig : 4 * (w + 1) ≤ epsilon
  · have h1 := h 1 zero_lt_one
    nlinarith
  · have hsmall : epsilon < 4 * (w + 1) := lt_of_not_ge hbig
    have hden : 0 < 4 * (w + 1) := by nlinarith
    let eta : ℝ := epsilon / (4 * (w + 1))
    have heta : 0 < eta := by
      dsimp [eta]
      exact div_pos hepsilon hden
    have heta_le : eta ≤ 1 := by
      dsimp [eta]
      apply (div_le_iff₀ hden).2
      simpa using hsmall.le
    have hηsq : eta ^ 2 ≤ eta := by nlinarith [sq_nonneg (eta - 1)]
    have heq : 4 * eta * (w + 1) = epsilon := by
      dsimp [eta]
      field_simp
    have hηw : 0 ≤ eta * w := mul_nonneg heta.le hw
    have hbound := h eta heta
    nlinarith

end PoincareConjecture
