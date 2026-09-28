import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Empty
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Gluing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Horn.Construction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularRegularLimit



theorem exists_limit_conclusion_of_terminal_canonical_threshold
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ (A : RepairedNeckCapTopologyTheory.{u})
        {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M), H.epsilon ≤ ε₀ →
        terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀ →
        (∀ hΩ : H.reference.regularLimitSet.Nonempty,
          ∀ x : ((H.nonemptyExtension P04 hΩ).extended.slice T).carrier,
            H.r₀⁻¹ ^ 2 < ((H.nonemptyExtension P04 hΩ).extended.connection T).scalarCurvature x →
              TerminalCanonicalNeighborhood (H.nonemptyExtension P04 hΩ) x
                (terminalAccuracyFactor * H.epsilon) (2 * H.constant)) →
        Nonempty (RepairedSingularRegularLimitData H) := by
  obtain ⟨εH, hεH, hsmall, hhorn⟩ := TerminalEnd.exists_strongHorn_threshold.{u}
  have hfactor := terminalAccuracyFactor_pos
  have htwo := two_le_terminalAccuracyFactor
  refine ⟨εH / terminalAccuracyFactor, div_pos hεH hfactor, ?_, ?_⟩
  · apply le_trans _ hsmall
    exact (div_le_iff₀ hfactor).2 (by nlinarith)
  intro A M _ _ _ _ _ _ _ _ F T H hε hA hcanonical
  classical
  by_cases hΩ : H.reference.regularLimitSet.Nonempty
  · let E := H.nonemptyExtension P04 hΩ
    have hcanonical' : ∀ x : (E.extended.slice T).carrier,
        H.r₀⁻¹ ^ 2 < (E.extended.connection T).scalarCurvature x →
          GeneralizedCanonicalControl (F := E.extended) T x
            (terminalAccuracyFactor * H.epsilon) (2 * H.constant) := hcanonical hΩ
    obtain ⟨hlower, hproper⟩ := H.extended_terminal_scalar_proper_and_bounded_below P04
    refine ⟨{
      regular_open := H.regularLimitSet_isOpen P04
      regular_eventually_bounded := H.regularLimitSet_eventually_bounded P04
      extension := E
      terminal_source := H.terminalSource P04
      terminal_source_image := H.terminalSource_image P04
      terminal_source_openEmbedding := H.terminalSource_openEmbedding P04
      terminal_source_smooth := H.terminalSource_smooth P04
      terminal_source_regular := H.terminalSource_regular P04
      terminal_time_iff := H.terminal_mem_extendedTimeInterval_iff P04
      terminal_metric := E.extended.metric T
      terminal_metric_eq := rfl
      terminal_scalar := (E.extended.connection T).scalarCurvature
      terminal_scalar_eq := rfl
      scalar_lower := hlower
      scalar_proper := hproper
      metric_limit_on_compacts := H.compactSingularMetricLimit_extended_terminal P04
      gluing_map := H.terminalGluingMap P04
      gluing_time := H.terminalGluingMap_time P04
      gluing_old := H.terminalGluingMap_old P04
      gluing_terminal := H.terminalGluingMap_terminal P04
      gluing_openEmbedding := H.terminalGluingMap_openEmbedding P04
      gluing_cover := H.terminalGluingMap_cover P04
      gluing_vertical_compatibility := H.terminalGluingMap_vertical_compatibility P04 hΩ
      component_paths := fun x => ⟨terminalComponentPath E x, rfl⟩
      end_tube := fun K e => hhorn E K e A
        (mul_pos hfactor H.epsilon_pos) (mul_pos (by norm_num) H.constant_pos)
        (by nlinarith [(le_div_iff₀ hfactor).1 hε]) hA hlower hproper hcanonical'
      canonical_neighborhood := hcanonical'
    }⟩
  · exact ⟨H.regularLimitOfEmpty (Set.not_nonempty_iff_eq_empty.mp hΩ)⟩

end PoincareConjecture.SingularRegularLimit
