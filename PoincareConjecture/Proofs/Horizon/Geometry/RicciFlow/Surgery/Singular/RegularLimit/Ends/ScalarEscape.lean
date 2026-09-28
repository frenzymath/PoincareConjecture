import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Assembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.TerminalGeometry








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalComponentPath

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T}


theorem isCompact_scalar_sublevel (K : TerminalComponentPath E)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ C : Set ℝ, IsCompact C →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' C)) (B : ℝ) :
    IsCompact {x : K.component | (E.extended.connection T).scalarCurvature x ≤ B} := by
  obtain ⟨L, hL⟩ := hlower
  have hclosed : IsClosed K.component := by
    rw [K.component_eq]
    exact isClosed_connectedComponent
  have heq : {x : K.component | (E.extended.connection T).scalarCurvature x ≤ B} =
      Subtype.val ⁻¹' ((E.extended.connection T).scalarCurvature ⁻¹' Icc L B) := by
    ext x
    exact ⟨fun hx => ⟨hL x, hx⟩, fun hx => hx.2⟩
  rw [heq]
  exact hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage (hproper (Icc L B) isCompact_Icc)

end PoincareConjecture.TerminalComponentPath

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}


theorem tail_subset_compl_exhaustion (e : TerminalEnd K) (n : ℕ) :
    e.tail n ⊆ (e.exhaustion n)ᶜ := by
  obtain ⟨x, _, hx⟩ := e.tail_component n
  rw [hx]
  exact connectedComponentIn_subset _ x


theorem exists_tail_scalar_gt (e : TerminalEnd K)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ C : Set ℝ, IsCompact C →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' C)) (B : ℝ) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∀ x ∈ e.tail m,
      B < (E.extended.connection T).scalarCurvature x := by
  obtain ⟨n, hn⟩ := e.exhaustion.exists_superset_of_isCompact
    (K.isCompact_scalar_sublevel hlower hproper B)
  refine ⟨n, fun m hnm x hx => ?_⟩
  apply lt_of_not_ge
  intro hscalar
  exact e.tail_subset_compl_exhaustion m hx
    (e.exhaustion.subset hnm (hn hscalar))


theorem eventually_scalar_gt (e : TerminalEnd K)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ C : Set ℝ, IsCompact C →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' C)) (B : ℝ) :
    ∀ᶠ n in atTop, ∀ x ∈ e.tail n, B < (E.extended.connection T).scalarCurvature x := by
  obtain ⟨n, hn⟩ := e.exists_tail_scalar_gt hlower hproper B
  exact eventually_atTop.mpr ⟨n, hn⟩

end PoincareConjecture.TerminalEnd

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem nonemptyExtension_end_scalar_escape (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (hΩ : H.reference.regularLimitSet.Nonempty)
    (K : TerminalComponentPath (H.nonemptyExtension P04 hΩ)) (e : TerminalEnd K) (B : ℝ) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∀ x ∈ e.tail m,
      B < ((H.nonemptyExtension P04 hΩ).extended.connection T).scalarCurvature x := by
  obtain ⟨hlower, hproper⟩ := H.extended_terminal_scalar_proper_and_bounded_below P04
  exact e.exists_tail_scalar_gt hlower hproper B

end PoincareConjecture.SingularTimeAssumptions
