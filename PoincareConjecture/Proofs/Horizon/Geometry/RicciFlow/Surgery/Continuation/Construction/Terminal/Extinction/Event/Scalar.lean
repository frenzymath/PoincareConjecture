import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.PreFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.CanonicalTail









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B

theorem rebase_uniform_scalar_tail (hempty : I.controlled_core = ∅)
    (r : Ico I.last_slab.start T) (a : ℝ) (ha : a < I.rho⁻¹ ^ 2) :
    ∃ s : ℝ, r.1 ≤ s ∧ s < T ∧ ∀ t ∈ Ico s T, ∀ x : (F.slice r.1).carrier,
      a < ((I.last_slab.rebaseFlow r).connection t).scalarCurvature x := by
  obtain ⟨s, _, hsT, htail⟩ := B.preterminal_uniform_scalar_tail hempty a ha
  refine ⟨max r.1 s, le_max_left _ _, max_lt r.2.2 hsT, ?_⟩
  intro t ht x
  rw [I.last_slab.rebaseFlow_scalar]
  exact htail t ⟨(le_max_right _ _).trans ht.1, ht.2⟩ _

theorem rebase_pointwise_strict_scalar_tail (hempty : I.controlled_core = ∅)
    (r : Ico I.last_slab.start T) (x : (F.slice r.1).carrier) :
    ∃ a : ℝ, I.rho⁻¹ ^ 2 < a ∧ ∃ s ∈ Ico r.1 T, ∀ t ∈ Ico s T,
      a < ((I.last_slab.rebaseFlow r).connection t).scalarCurvature x := by
  obtain ⟨a, ha, s, _, hsT, htail⟩ :=
    B.preterminal_pointwise_strict_scalar_tail hempty ((I.last_slab.identify r).symm x)
  refine ⟨a, ha, max r.1 s, ⟨le_max_left _ _, max_lt r.2.2 hsT⟩, ?_⟩
  intro t ht
  rw [I.last_slab.rebaseFlow_scalar]
  exact htail t ⟨(le_max_right _ _).trans ht.1, ht.2⟩

theorem exists_rebase_canonical_tail (hempty : I.controlled_core = ∅)
    (r : Ico I.last_slab.start T) :
    ∃ s : ℝ, r.1 < s ∧ s < T ∧ ∀ t ∈ Ico s T, ∀ x : (F.slice t).carrier,
      SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
  obtain ⟨s, _, hsT, hcanonical⟩ := B.exists_canonical_tail hempty
  obtain ⟨s', hss', hs'T⟩ := exists_between (max_lt r.2.2 hsT)
  refine ⟨s', (le_max_left _ _).trans_lt hss', hs'T, ?_⟩
  intro t ht x
  exact hcanonical t ⟨((le_max_right _ _).trans hss'.le).trans ht.1, ht.2⟩ x

end PoincareConjecture.RepairedContinuationLimitBridge
