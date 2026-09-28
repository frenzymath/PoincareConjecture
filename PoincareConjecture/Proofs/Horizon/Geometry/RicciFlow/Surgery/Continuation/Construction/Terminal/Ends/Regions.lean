import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CanonicalCover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness

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

theorem isCompact_closed_subset_cap (Q : SingularLimitConclusion H)
    (cap : CapCertificate (Q.extension.extended.metric T))
    {X : Set (Q.extension.extended.slice T).carrier}
    (hclosed : IsClosed X) (hsub : X ⊆ cap.carrier) : IsCompact X := by
  by_cases hX : X.Nonempty
  · obtain ⟨x, hx⟩ := hX
    obtain ⟨bound, hbound, hratio⟩ := cap.scalar_ratio
    apply (Q.isCompact_scalar_sublevel (bound * cap.connection.scalarCurvature x)).of_isClosed_subset
      hclosed
    intro y hy
    change (Q.extension.extended.connection T).scalarCurvature y ≤
      bound * cap.connection.scalarCurvature x
    rw [← cap.connection.scalarCurvature_eq (Q.extension.extended.connection T) y]
    exact hratio x (hsub hx) y (hsub hy)
  · simpa only [Set.not_nonempty_iff_eq_empty.mp hX] using isCompact_empty

theorem tube_or_cappedTube_of_noncompact (Q : SingularLimitConclusion H)
    (C : ConnectedNeckCapCover (Q.extension.extended.metric T))
    (R : RepairedNeckCapTopologyData (Q.extension.extended.metric T) C)
    (hclosed : IsClosed C.X) (hnoncompact : ¬ IsCompact C.X) :
    (∃ tube : EpsilonTubeCertificate (Q.extension.extended.metric T) C.X,
      tube.epsilon = C.epsilon) ∨
    ∃ capped : CappedTubeCertificate (Q.extension.extended.metric T),
      C.X ⊆ capped.carrier ∧ capped.cap.epsilon = C.epsilon ∧
      capped.tube.epsilon = C.epsilon ∧ capped.cap.cap_constant ≤ C.cap_constant := by
  rcases R with ⟨R, hR⟩
  cases R with
  | twoCaps kind cap₁ cap₂ component hunion hcontains =>
      exact (hnoncompact (component.compact.of_isClosed_subset hclosed hcontains)).elim
  | doubleCappedTube certificate kind component hcontains =>
      exact (hnoncompact (certificate.compact.of_isClosed_subset hclosed hcontains)).elim
  | singleCap cap hcontains =>
      exact (hnoncompact (Q.isCompact_closed_subset_cap cap hclosed hcontains)).elim
  | cappedTube certificate hcontains =>
      exact Or.inr ⟨certificate, hcontains, hR.1, hR.2.1, hR.2.2.1⟩
  | tube tube => exact Or.inl ⟨tube, hR⟩
  | fibration fibration =>
      exact (hnoncompact (fibration.compact.of_isClosed_subset hclosed
        fibration.contains_X)).elim

end PoincareConjecture.SingularLimitConclusion
