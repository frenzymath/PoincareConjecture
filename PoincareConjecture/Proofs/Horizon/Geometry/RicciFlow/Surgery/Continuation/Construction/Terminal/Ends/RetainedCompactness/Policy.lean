import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.Cover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Retained.Policy








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}

theorem isCompact_closure_policyRetainedOpen (Q : SingularLimitConclusion H) (rho : ℝ)
    {ι : Type u} [Finite ι] {C : MetricSurgeryConstants}
    (J : ι → MetricSurgeryInput C (Q.extension.extended.metric T))
    (cuts : ∀ i, SurgeryEndCut (J i).neck)
    (hcover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ (cuts i).tail) :
    IsCompact (closure (Surgery.Terminal.Gluing.policyRetainedOpen
      (Q.extension.extended.connection T) rho J cuts :
        Set (Q.extension.extended.slice T).carrier)) := by
  exact (Q.isCompact_retained_of_end_cut_cover rho (fun i => (J i).neck) cuts hcover).of_isClosed_subset
      isClosed_closure
      (Surgery.Terminal.Gluing.closure_policyRetainedOpen_subset
        (Q.extension.extended.connection T) rho J cuts)

end PoincareConjecture.SingularLimitConclusion
