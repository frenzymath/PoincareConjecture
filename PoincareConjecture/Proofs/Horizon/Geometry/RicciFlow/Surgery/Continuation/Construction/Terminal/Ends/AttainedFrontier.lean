import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.IntersectingRegions

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

theorem calibrated_neck_or_cap_at_linear_level (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀)
    (hconstant : 1 ≤ H.constant)
    {x : (Q.extension.extended.slice T).carrier} (hx : x ∈ K.component)
    (hlevel : Q.terminal_scalar x = 2 * H.constant * rho⁻¹ ^ 2) :
    (∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x ∧
      Disjoint N.carrier {y | Q.terminal_scalar y ≤ rho⁻¹ ^ 2} ∧
      ∀ y ∈ N.central_sphere, Q.terminal_scalar y ≤ (rho / (2 * H.constant))⁻¹ ^ 2) ∨
    (∃ cap : CapCertificate (Q.extension.extended.metric T),
      cap.epsilon = terminalAccuracyFactor * H.epsilon ∧ cap.cap_constant ≤ 2 * H.constant ∧
      cap.connection = Q.extension.extended.connection T ∧ x ∈ cap.core ∧
      Disjoint cap.carrier {y | Q.terminal_scalar y ≤ rho⁻¹ ^ 2} ∧
      IsCompact (closure cap.carrier) ∧
      ∀ y ∈ cap.carrier, Q.terminal_scalar y < (rho / (2 * H.constant))⁻¹ ^ 2) := by
  have hcanonical : H.r₀⁻¹ ^ 2 < Q.terminal_scalar x := by
    rw [hlevel]
    have hrho_sq : 0 < rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hrho)
    have hr₀_sq : H.r₀⁻¹ ^ 2 ≤ rho⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr H.r₀_pos.le)
        ((inv_le_inv₀ H.r₀_pos hrho).mpr hrho_r₀.le) 2
    nlinarith [mul_le_mul_of_nonneg_right hconstant hrho_sq.le]
  rcases Q.neck_or_cap_on_end_component K e hx hcanonical with
    ⟨N, hN⟩ | ⟨cap, hε, hC, hconnection, hcore⟩
  · left
    have hhalf : terminalAccuracyFactor * H.epsilon < 1 / 2 :=
      H.terminal_epsilon_le_threshold.trans_lt (by norm_num)
    have hxN : x ∈ N.carrier := hN ▸ N.central_sphere_subset N.center_on_central_sphere
    refine ⟨N, hN, Q.neck_disjoint_low_core_of_high_point (N.spatialNeck hhalf)
      H.terminal_epsilon_le_threshold rho hconstant ⟨x, hxN, hlevel.ge⟩, ?_⟩
    apply Q.neck_central_sphere_below_calibrated_level N rho
    rw [hN, hlevel]
    have hC : H.constant ≤ H.constant ^ 2 := by nlinarith [sq_nonneg (H.constant - 1)]
    nlinarith [mul_le_mul_of_nonneg_right hC (sq_nonneg rho⁻¹)]
  · right
    have hxcap := cap.core_subset_carrier hcore
    have hupper := Q.cap_below_calibrated_level_of_linear_low_point cap rho hC
      ⟨x, hxcap, hlevel.le⟩
    refine ⟨cap, hε, hC, hconnection, hcore,
      Q.cap_disjoint_low_core_of_linear_high_point cap rho hC
        ⟨x, hxcap, hlevel.ge⟩, ?_, hupper⟩
    apply Q.isCompact_closure_of_scalar_bound cap.carrier ((rho / (2 * H.constant))⁻¹ ^ 2)
    intro y hy
    rw [← Q.terminal_scalar_eq]
    exact (hupper y hy).le

end PoincareConjecture.SingularLimitConclusion
