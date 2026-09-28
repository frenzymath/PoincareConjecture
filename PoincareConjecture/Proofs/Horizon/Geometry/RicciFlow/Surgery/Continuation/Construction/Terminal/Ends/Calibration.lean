import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CanonicalCover

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_calibrated_end_region (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀)
    (hconstant : 1 ≤ H.constant)
    (hcore : ∃ x ∈ K.component, Q.terminal_scalar x ≤ rho⁻¹ ^ 2) :
    ∃ (n : ℕ) (X : Set (Q.extension.extended.slice T).carrier),
      IsClosed X ∧ IsConnected X ∧ X ⊆ K.component ∧
      Subtype.val '' e.tail n ⊆ X ∧ ¬ IsCompact X ∧
      (∀ x ∈ X, 2 * H.constant ^ 2 * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x) ∧
      (∀ x ∈ X, H.r₀⁻¹ ^ 2 < Q.terminal_scalar x) ∧
      ∃ x ∈ X, Q.terminal_scalar x = 2 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
  have hrho_sq : 0 < rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hrho)
  have hC_sq : 1 ≤ H.constant ^ 2 := by
    nlinarith [sq_nonneg (H.constant - 1)]
  have hlevel : rho⁻¹ ^ 2 < 2 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hC_sq hrho_sq.le]
  have hr₀_sq : H.r₀⁻¹ ^ 2 ≤ rho⁻¹ ^ 2 := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr H.r₀_pos.le)
      ((inv_le_inv₀ H.r₀_pos hrho).mpr hrho_r₀.le) 2
  obtain ⟨n, X, hclosed, hconn, hsub, htail, hnoncompact, hlower, hattain⟩ :=
    Q.exists_end_superlevel_region K e (2 * H.constant ^ 2 * rho⁻¹ ^ 2)
      (by obtain ⟨x, hx, hcurv⟩ := hcore; exact ⟨x, hx, hcurv.trans_lt hlevel⟩)
  exact ⟨n, X, hclosed, hconn, hsub, htail, hnoncompact, hlower,
    fun x hx => hr₀_sq.trans_lt (hlevel.trans_le (hlower x hx)), hattain⟩

end PoincareConjecture.SingularLimitConclusion
