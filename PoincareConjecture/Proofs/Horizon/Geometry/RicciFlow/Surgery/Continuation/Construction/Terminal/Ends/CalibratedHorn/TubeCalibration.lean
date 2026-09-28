import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeStrongCenters









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

theorem exists_calibrated_strong_neck_in_tube (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier)
    (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) X)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀)
    (hconstant : 2 ≤ H.constant) (hclosed : IsClosed X)
    (hcomponent : X ⊆ K.component)
    (hfront : ∀ x ∈ frontier X, Q.terminal_scalar x = rho⁻¹ ^ 2)
    {x : (Q.extension.extended.slice T).carrier} (hx : x ∈ X)
    (hlevel : Q.terminal_scalar x = 4 * H.constant * rho⁻¹ ^ 2) :
    ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x ∧
      N.carrier ⊆ interior X ∧
      Disjoint N.carrier {y | Q.terminal_scalar y ≤ rho⁻¹ ^ 2} ∧
      (∀ y ∈ N.carrier,
        ∃ P : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), P.center = y) ∧
      (∀ y ∈ N.carrier, Q.terminal_scalar y < 8 * H.constant * rho⁻¹ ^ 2) ∧
      ∀ y ∈ N.central_sphere,
        Q.terminal_scalar y < (rho / (2 * H.constant))⁻¹ ^ 2 := by
  have hqpos : 0 < rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hrho)
  have hq : H.r₀⁻¹ ^ 2 < rho⁻¹ ^ 2 := by
    have hinv := (inv_lt_inv₀ H.r₀_pos hrho).mpr hrho_r₀
    nlinarith [inv_pos.mpr H.r₀_pos, inv_pos.mpr hrho]
  have hC : 1 ≤ H.constant := by linarith
  have htwice : 2 * H.constant * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x := by
    rw [hlevel]
    nlinarith [mul_pos H.constant_pos hqpos]
  have hscalar : H.r₀⁻¹ ^ 2 < Q.terminal_scalar x := by
    rw [hlevel]
    nlinarith [mul_le_mul_of_nonneg_right hC hqpos.le]
  obtain ⟨N, hN⟩ := Q.strong_neck_center_of_tube_high_point K e X tube
    (rho⁻¹ ^ 2) hclosed hcomponent hfront hx hscalar htwice
  have hhigh : 4 * H.constant * rho⁻¹ ^ 2 ≤ Q.terminal_scalar N.center := by
    rw [hN, hlevel]
  obtain ⟨hsub, hcenters⟩ :=
    Q.strong_neck_carrier_has_strong_centers_of_tube_high_center K e X tube
      (rho⁻¹ ^ 2) hq hC hclosed hcomponent hfront N (hN ▸ hx) hhigh
  have hbound (y) (hy : y ∈ N.carrier) :
      Q.terminal_scalar y < 8 * H.constant * rho⁻¹ ^ 2 := by
    have h := (N.scalar_strictly_within_factor_two_on_carrier
      H.terminal_epsilon_le_threshold hy).2
    rw [← Q.terminal_scalar_eq, hN, hlevel] at h
    nlinarith
  have hhalf : terminalAccuracyFactor * H.epsilon < 1 / 2 :=
    H.terminal_epsilon_le_threshold.trans_lt (by norm_num)
  refine ⟨N, hN, hsub, ?_, hcenters, hbound, ?_⟩
  · exact Q.neck_disjoint_low_core_of_high_point (N.spatialNeck hhalf)
      H.terminal_epsilon_le_threshold rho hC
      ⟨N.center, N.central_sphere_subset N.center_on_central_sphere, hN.symm ▸ htwice⟩
  · intro y hy
    have h := hbound y (N.central_sphere_subset hy)
    have hCsq : 2 * H.constant ≤ H.constant ^ 2 := by
      nlinarith [H.constant_pos]
    have hmul := mul_le_mul_of_nonneg_right hCsq hqpos.le
    have hid : (rho / (2 * H.constant))⁻¹ ^ 2 =
        4 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
      rw [inv_div, div_eq_mul_inv]
      ring
    rw [hid]
    nlinarith

end PoincareConjecture.SingularLimitConclusion
