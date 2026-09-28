import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.CapContainment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.CapNoncontainment









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

theorem strong_neck_center_of_tube_high_point (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier)
    (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) X)
    (q : ℝ) (hclosed : IsClosed X) (hcomponent : X ⊆ K.component)
    (hfront : ∀ x ∈ frontier X, Q.terminal_scalar x = q)
    {x : (Q.extension.extended.slice T).carrier} (hx : x ∈ X)
    (hcanonical : H.r₀⁻¹ ^ 2 < Q.terminal_scalar x)
    (hhigh : 2 * H.constant * q ≤ Q.terminal_scalar x) :
    ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x := by
  rcases Q.neck_or_cap_on_end_component K e (hcomponent hx) hcanonical with
    hneck | ⟨cap, hepsilon, hconstant, _, hcore⟩
  · exact hneck
  · have hxcap := cap.core_subset_carrier hcore
    have hcap := Q.cap_subset_interior_of_linear_high_point cap X q hclosed hfront
      ⟨x, hxcap, hx⟩ hconstant ⟨x, hxcap, hhigh⟩
    exact (cap.tube_noncontainment_of_epsilon_le tube
      (hepsilon.trans_le H.terminal_epsilon_le_threshold) tube.epsilon_le_threshold
      (hcap.trans (interior_subset.trans tube.contains_X))).elim

theorem strong_neck_carrier_has_strong_centers_of_tube_high_center
    (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier)
    (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) X)
    (q : ℝ) (hq : H.r₀⁻¹ ^ 2 < q) (hconstant : 1 ≤ H.constant)
    (hclosed : IsClosed X) (hcomponent : X ⊆ K.component)
    (hfront : ∀ x ∈ frontier X, Q.terminal_scalar x = q)
    (N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon))
    (hcenter : N.center ∈ X)
    (hhigh : 4 * H.constant * q ≤ Q.terminal_scalar N.center) :
    N.carrier ⊆ interior X ∧ ∀ x ∈ N.carrier,
      ∃ P : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), P.center = x := by
  have hqpos : 0 < q := lt_of_le_of_lt (sq_nonneg _) hq
  have hlevel : q ≤ 2 * H.constant * q := by
    nlinarith [mul_le_mul_of_nonneg_right hconstant hqpos.le]
  have hNhigh (x) (hx : x ∈ N.carrier) : 2 * H.constant * q < Q.terminal_scalar x := by
    have h := (N.scalar_strictly_within_factor_two_on_carrier
      H.terminal_epsilon_le_threshold hx).1
    rw [← Q.terminal_scalar_eq] at h
    linarith
  have hdisjoint : Disjoint N.carrier (frontier X) := by
    refine disjoint_left.mpr fun x hx hxf => ?_
    exact (hlevel.trans_lt (hNhigh x hx)).ne' (hfront x hxf)
  have hsub : N.carrier ⊆ interior X := by
    apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      N.isPreconnected_carrier hdisjoint
    refine ⟨N.center, N.central_sphere_subset N.center_on_central_sphere, ?_⟩
    by_contra hni
    exact disjoint_left.mp hdisjoint
      (N.central_sphere_subset N.center_on_central_sphere)
      ⟨subset_closure hcenter, hni⟩
  refine ⟨hsub, fun x hx => ?_⟩
  exact Q.strong_neck_center_of_tube_high_point K e X tube q hclosed hcomponent
    hfront (interior_subset (hsub hx)) (hq.trans (hlevel.trans_lt (hNhigh x hx)))
    (hNhigh x hx).le

end PoincareConjecture.SingularLimitConclusion
