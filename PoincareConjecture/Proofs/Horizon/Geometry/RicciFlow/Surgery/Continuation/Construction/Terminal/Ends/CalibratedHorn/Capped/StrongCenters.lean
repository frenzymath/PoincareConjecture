import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.Nesting
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.MixedOverlap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.CapContainment

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

theorem strong_neck_center_of_cappedTube_high_point (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    (hY : Y.carrier = K.component)
    (hYepsilon : Y.cap.epsilon = terminalAccuracyFactor * H.epsilon)
    (hYconstant : Y.cap.cap_constant ≤ 2 * H.constant)
    (q : ℝ) {p : (Q.extension.extended.slice T).carrier}
    (hp : p ∈ Y.cap.carrier) (hplow : Q.terminal_scalar p ≤ q)
    {x : (Q.extension.extended.slice T).carrier} (hx : x ∈ K.component)
    (hcanonical : H.r₀⁻¹ ^ 2 < Q.terminal_scalar x)
    (hhigh : 2 * H.constant * q ≤ Q.terminal_scalar x) :
    ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x := by
  rcases Q.neck_or_cap_on_end_component K e hx hcanonical with
    hneck | ⟨D, hDepsilon, hDconstant, _, hxcore⟩
  · exact hneck
  · have hYscalar (z) : Y.cap.connection.scalarCurvature z = Q.terminal_scalar z := by
      rw [Q.terminal_scalar_eq]
      exact Y.cap.connection.scalarCurvature_eq _ z
    have hpR : 0 < Q.terminal_scalar p := by
      rw [← hYscalar]
      exact Y.cap.scalar_pos p hp
    have hYupper (y) (hy : y ∈ Y.cap.carrier) :
        Q.terminal_scalar y < 2 * H.constant * q := by
      have h := Y.cap.scalar_lt_constant_mul hp hy
      rw [hYscalar y, hYscalar p] at h
      exact h.trans_le ((mul_le_mul_of_nonneg_right hYconstant hpR.le).trans
        (mul_le_mul_of_nonneg_left hplow
          (mul_nonneg (by norm_num) H.constant_pos.le)))
    have hxout : x ∉ Y.cap.carrier := fun hxC => (hYupper x hxC).not_ge hhigh
    have hDhigh := Q.cap_scalar_gt_of_linear_high_point D q hDconstant
      ⟨x, D.core_subset_carrier hxcore, hhigh⟩
    have hpout : p ∉ D.carrier := fun hpD => (hDhigh p hpD).not_ge hplow
    have hxcomp : connectedComponent x = K.component := by
      rw [K.component_eq] at hx ⊢
      exact (connectedComponent_eq hx).symm
    have hDcore : D.closed_core ⊆ Y.carrier := by
      rw [hY, ← hxcomp]
      exact D.closed_core_subset_carrier.trans
        (D.isConnected_carrier.isPreconnected.subset_connectedComponent
          (D.core_subset_carrier hxcore))
    have hcontact := D.frontier_core_contact_of_cappedTube Y hDcore ⟨hxcore, hxout⟩
    have hnot : ¬ Y.cap.carrier ⊆ D.carrier := fun h => hpout (h hp)
    have hcomponent : connectedComponent Y.cap.boundary_neck.center = K.component := by
      have hc : Y.cap.boundary_neck.center ∈ K.component := hY ▸ Y.cap_subset
        (Y.cap.boundary_neck_subset (Y.cap.boundary_neck.central_sphere_subset
          Y.cap.boundary_neck.center_on_central_sphere))
      rw [K.component_eq] at hc ⊢
      exact (connectedComponent_eq hc).symm
    have hnoncompact : ¬ IsCompact (connectedComponent Y.cap.boundary_neck.center) :=
      hcomponent.symm ▸ e.not_isCompact_component
    obtain ⟨hmeet, hmiss⟩ := Y.cap.mixed_boundary_of_frontier_core_contact_of_noncompact
      D hnoncompact hcontact hnot
    rcases Y.cap.mixed_overlap_containment_or_closing_of_epsilon_le D
        Y.cap.epsilon_le_threshold (hDepsilon.trans hYepsilon.symm) hmeet hmiss with
      hcontain | ⟨heq, hcompact⟩
    · exact (hnot hcontain).elim
    · exact (hnoncompact (heq ▸ hcompact)).elim

end PoincareConjecture.SingularLimitConclusion
