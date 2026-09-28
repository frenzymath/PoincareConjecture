import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CanonicalCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.ConstantLower
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Connected








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



theorem cap_scalar_gt_of_linear_high_point (Q : SingularLimitConclusion H)
    (cap : CapCertificate (Q.extension.extended.metric T))
    (q : ℝ) (hcap : cap.cap_constant ≤ 2 * H.constant)
    (hhigh : ∃ x ∈ cap.carrier, 2 * H.constant * q ≤ Q.terminal_scalar x) :
    ∀ y ∈ cap.carrier, q < Q.terminal_scalar y := by
  obtain ⟨x, hx, hxhigh⟩ := hhigh
  have heq (z) : cap.connection.scalarCurvature z = Q.terminal_scalar z := by
    rw [Q.terminal_scalar_eq]
    exact cap.connection.scalarCurvature_eq _ z
  intro y hy
  by_contra h
  have hylow : Q.terminal_scalar y ≤ q := le_of_not_gt h
  have hratio := cap.scalar_lt_constant_mul hy hx
  rw [heq x, heq y] at hratio
  have hpos : 0 < Q.terminal_scalar y := by
    rw [← heq y]
    exact cap.scalar_pos y hy
  have hupper := (mul_le_mul_of_nonneg_right hcap hpos.le).trans
    (mul_le_mul_of_nonneg_left hylow
      (by positivity [H.constant_pos] : 0 ≤ 2 * H.constant))
  exact (not_lt_of_ge hxhigh) (hratio.trans_le hupper)



theorem cap_subset_interior_of_frontier_scalar (Q : SingularLimitConclusion H)
    (cap : CapCertificate (Q.extension.extended.metric T))
    (X : Set (Q.extension.extended.slice T).carrier) (q : ℝ)
    (hclosed : IsClosed X)
    (hfront : ∀ x ∈ frontier X, Q.terminal_scalar x = q)
    (hmeet : (cap.carrier ∩ X).Nonempty)
    (hhigh : ∀ x ∈ cap.carrier, q < Q.terminal_scalar x) :
    cap.carrier ⊆ interior X := by
  have hdisjoint : Disjoint cap.carrier (frontier X) := by
    refine disjoint_left.mpr fun x hx hxf => ?_
    exact (hhigh x hx).ne' (hfront x hxf)
  apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    cap.isConnected_carrier.isPreconnected hdisjoint
  obtain ⟨x, hx, hxX⟩ := hmeet
  refine ⟨x, hx, ?_⟩
  by_contra hxi
  apply disjoint_left.mp hdisjoint hx
  exact ⟨by rwa [hclosed.closure_eq], hxi⟩



theorem cap_subset_interior_of_linear_high_point (Q : SingularLimitConclusion H)
    (cap : CapCertificate (Q.extension.extended.metric T))
    (X : Set (Q.extension.extended.slice T).carrier) (q : ℝ)
    (hclosed : IsClosed X)
    (hfront : ∀ x ∈ frontier X, Q.terminal_scalar x = q)
    (hmeet : (cap.carrier ∩ X).Nonempty)
    (hcap : cap.cap_constant ≤ 2 * H.constant)
    (hhigh : ∃ x ∈ cap.carrier, 2 * H.constant * q ≤ Q.terminal_scalar x) :
    cap.carrier ⊆ interior X :=
  Q.cap_subset_interior_of_frontier_scalar cap X q hclosed hfront hmeet
    (Q.cap_scalar_gt_of_linear_high_point cap q hcap hhigh)



theorem constant_gt_ninetyNine_of_terminal_cap (Q : SingularLimitConclusion H)
    (cap : CapCertificate (Q.extension.extended.metric T))
    (hcap : cap.cap_constant ≤ 2 * H.constant) : 99 < H.constant := by
  linarith [cap.oneHundredNinetyEight_lt_constant]

theorem no_terminal_cap_of_constant_le_ninetyNine (Q : SingularLimitConclusion H)
    (hconstant : H.constant ≤ 99) :
    ¬ ∃ cap : CapCertificate (Q.extension.extended.metric T),
      cap.cap_constant ≤ 2 * H.constant := by
  rintro ⟨cap, hcap⟩
  exact (Q.constant_gt_ninetyNine_of_terminal_cap cap hcap).not_ge hconstant



theorem neck_on_end_component_of_constant_le_ninetyNine
    (Q : SingularLimitConclusion H) (hconstant : H.constant ≤ 99)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    {x : (Q.extension.extended.slice T).carrier} (hx : x ∈ K.component)
    (hscalar : H.r₀⁻¹ ^ 2 < Q.terminal_scalar x) :
    ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x := by
  rcases Q.neck_or_cap_on_end_component K e hx hscalar with
    hneck | ⟨cap, _, hcap, _, _⟩
  · exact hneck
  · exact (Q.no_terminal_cap_of_constant_le_ninetyNine hconstant ⟨cap, hcap⟩).elim

end PoincareConjecture.SingularLimitConclusion
