import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.Ambient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CapCurvature

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem scalar_strictly_within_factor_two_on_carrier
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hε : N.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.carrier) :
    D.scalarCurvature N.center / 2 < D.scalarCurvature x ∧
      D.scalarCurvature x < 2 * D.scalarCurvature N.center := by
  have hc := abs_lt.mp (N.abs_scaled_scalar_sub_one_lt_half_on_carrier D hε hx)
  have hn := N.scale_sq_mul_scalar_center_of_connection D
  have hscale := sq_pos_of_pos N.scale_pos
  constructor
  · apply (mul_lt_mul_iff_right₀ hscale).mp
    nlinarith only [hc.1, hn]
  · apply (mul_lt_mul_iff_right₀ hscale).mp
    nlinarith only [hc.2, hn]

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.GeneralizedStrongNeck

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}

theorem scalar_strictly_within_factor_two_on_carrier
    (N : GeneralizedStrongNeck F T epsilon) (hε : epsilon ≤ 1 / 200)
    {x : (F.slice T).carrier} (hx : x ∈ N.carrier) :
    (F.connection T).scalarCurvature N.center / 2 < (F.connection T).scalarCurvature x ∧
      (F.connection T).scalarCurvature x < 2 * (F.connection T).scalarCurvature N.center :=
  (N.spatialNeck (hε.trans_lt (by norm_num))).scalar_strictly_within_factor_two_on_carrier
    (F.connection T) hε hx

end PoincareConjecture.GeneralizedStrongNeck

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem neck_disjoint_low_core_of_high_center (Q : SingularLimitConclusion H)
    (N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon))
    (rho : ℝ) (hconstant : 1 ≤ H.constant)
    (hhigh : 2 * H.constant ^ 2 * rho⁻¹ ^ 2 ≤ Q.terminal_scalar N.center) :
    Disjoint N.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} := by
  refine disjoint_left.mpr fun x hx hlow => ?_
  have hstrict := (N.scalar_strictly_within_factor_two_on_carrier
    H.terminal_epsilon_le_threshold hx).1
  rw [← Q.terminal_scalar_eq] at hstrict
  have hC : 1 ≤ H.constant ^ 2 := by nlinarith [sq_nonneg (H.constant - 1)]
  have hprod := mul_le_mul_of_nonneg_right hC (sq_nonneg rho⁻¹)
  change Q.terminal_scalar x ≤ rho⁻¹ ^ 2 at hlow
  nlinarith

theorem neck_central_sphere_below_calibrated_level (Q : SingularLimitConclusion H)
    (N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon))
    (rho : ℝ) (hcenter : Q.terminal_scalar N.center ≤ 2 * H.constant ^ 2 * rho⁻¹ ^ 2) :
    ∀ x ∈ N.central_sphere,
      Q.terminal_scalar x ≤ (rho / (2 * H.constant))⁻¹ ^ 2 := by
  intro x hx
  have hstrict := (N.scalar_strictly_within_factor_two_on_carrier
    H.terminal_epsilon_le_threshold (N.central_sphere_subset hx)).2
  rw [← Q.terminal_scalar_eq] at hstrict
  have hscale : (rho / (2 * H.constant))⁻¹ ^ 2 = 4 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
    rw [inv_div, div_eq_mul_inv]
    ring
  rw [hscale]
  linarith

theorem hornBoundaryBelow_of_calibrated_neck (Q : SingularLimitConclusion H)
    (horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon))
    (N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon))
    (hsphere : N.central_sphere = horn.boundary_sphere)
    (rho : ℝ) (hcenter : Q.terminal_scalar N.center ≤ 2 * H.constant ^ 2 * rho⁻¹ ^ 2) :
    HornBoundaryBelow horn (rho / (2 * H.constant)) := by
  intro x hx
  rw [← Q.terminal_scalar_eq]
  exact Q.neck_central_sphere_below_calibrated_level N rho hcenter x (hsphere.symm ▸ hx)

theorem endRegionCover_neck_disjoint_low_core (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u})
    (haccuracy : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier) (hX : IsConnected X)
    (hcomponent : X ⊆ K.component)
    (hscalar : ∀ x ∈ X, H.r₀⁻¹ ^ 2 < Q.terminal_scalar x)
    (rho : ℝ) (hconstant : 1 ≤ H.constant)
    (hlower : ∀ x ∈ X, 2 * H.constant ^ 2 * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x)
    (N : EpsilonNeck (Q.extension.extended.metric T))
    (hN : N ∈ (Q.endRegionCover A haccuracy K e X hX hcomponent hscalar).necks) :
    Disjoint N.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} := by
  obtain ⟨S, rfl, hS⟩ := hN
  exact Q.neck_disjoint_low_core_of_high_center S rho hconstant (hlower S.center hS)

end PoincareConjecture.SingularLimitConclusion
