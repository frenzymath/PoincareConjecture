import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.RetainedCompactness.TerminalEnd
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CoreComponents
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CutTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.EndCorrespondence









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  (Q : SingularLimitConclusion H) (rho : ℝ)



theorem isCompact_core_diff_of_end_tail_cover
    {V : Set (Q.extension.extended.slice T).carrier} (hV : IsOpen V)
    (hcover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ n, Subtype.val '' e.tail n ⊆ V) :
    IsCompact (SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho \ V) := by
  obtain ⟨points, hpoints, hcore⟩ := Q.exists_finite_core_components rho
  have hpieces : ∀ p ∈ points, IsCompact (connectedComponent p \ V) := by
    intro p hp
    obtain ⟨K, hK⟩ := Q.component_paths p
    have hcomp : K.component = connectedComponent p := by rw [K.component_eq, hK]
    have hlow : (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty :=
      ⟨p, hcomp.symm ▸ mem_connectedComponent, hpoints p hp⟩
    simpa only [hcomp] using K.isCompact_diff_of_end_tail_cover hV (hcover K hlow)
  have heq : SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho \ V =
      ⋃ p ∈ points, connectedComponent p \ V := by
    rw [hcore]
    ext x
    simp only [mem_sdiff, mem_iUnion]
    aesop
  rw [heq]
  exact points.isCompact_biUnion hpieces



theorem isCompact_retained_of_end_cut_cover {ι : Type*}
    (N : ι → EpsilonNeck (Q.extension.extended.metric T))
    (cuts : ∀ i, SurgeryEndCut (N i))
    (hcover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ (cuts i).tail) :
    IsCompact (SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho \
      ⋃ i, (cuts i).tail) := by
  apply Q.isCompact_core_diff_of_end_tail_cover rho
    (isOpen_iUnion fun i => (cuts i).tail_isOpen)
  intro K hK e
  obtain ⟨i, n, hn⟩ := hcover K hK e
  exact ⟨n, fun x hx => mem_iUnion.mpr ⟨i, hn hx⟩⟩



theorem isCompact_retained_of_horn_end_cover {ι : Type*} {epsilon delta : ℝ}
    (horn : ι → StrongHorn Q.extension epsilon)
    (N : ι → TerminalStrongNeck Q.extension delta)
    (hornCuts : ∀ i, HornEndCut (horn i) (N i) rho)
    (P : ι → EpsilonNeck (Q.extension.extended.metric T))
    (cuts : ∀ i, SurgeryEndCut (P i))
    (htail : ∀ i, (cuts i).tail = (hornCuts i).carrier)
    (hcover : ∀ K : TerminalComponentPath Q.extension,
      (K.component ∩ {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2}).Nonempty →
      ∀ e : TerminalEnd K, ∃ i n, Subtype.val '' e.tail n ⊆ (horn i).carrier) :
    IsCompact (SurgeryTerminalCoreComponents (Q.extension.extended.connection T) rho \
      ⋃ i, (cuts i).tail) := by
  apply Q.isCompact_retained_of_end_cut_cover rho P cuts
  intro K hK e
  obtain ⟨i, n, hn⟩ := hcover K hK e
  obtain ⟨m, _, hm⟩ := e.exists_tail_subset_hornEndCut (hornCuts i) n hn
  exact ⟨i, m, (htail i).symm ▸ hm⟩

end PoincareConjecture.SingularLimitConclusion
