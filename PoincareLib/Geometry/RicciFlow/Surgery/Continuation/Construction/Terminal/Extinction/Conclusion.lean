import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Operation

/-!
# Permanent-extinction continuation from an empty controlled core

The constructed vanishing operation extends the original flow to every
nonnegative time, with no later surgery and no nonempty post-terminal slice.
The event uses the proved fixed-epsilon round sectional positivity theorem.
Source: Morgan--Tian, Definition 15.8 and Theorem 15.9, pp. 361-363,
and Section 17.2, p. 409.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.RepairedContinuationLimitBridge

open Surgery.Extinction

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)
  (hempty : I.controlled_core = ∅)

def extinctionConclusion : RepairedContinuationConclusion I := by
  let V := B.vanishingEvent hempty
  let V' := canonicalVanishingEvent I V
  let hV := B.vanishingEvent_slab_compatibility hempty
  let E := B.extinctionExtension hempty
  let he := B.extinction_terminal_empty hempty
  refine {
    extension := E
    old_event_data := old_event_preservation I V' hV
    end_time := ⊤
    extends_past := ENNReal.ofReal_lt_top
    time_domain_eq := rfl
    surgery_at_terminal := B.extinction_surgery_at_terminal hempty
    terminal_operation := .vanishing he
      (B.extinctionOperation hempty)
    terminal_nonempty_iff := ?_
    terminal_empty_iff := ⟨fun _ => he, fun _ => hempty⟩
    terminal_empty_end_time_top := fun _ => rfl
    post_terminal_interval := post_terminal_interval I V' hV
    admissible := admissible I V hV
    pinched := pinched I V' hV
    extinction_permanent := E.extended.extinction_permanent
    no_later_surgery := fun t _ht ht => no_later_surgery I V' hV t ht
    finite_end_slab := fun h => (h rfl).elim }
  constructor
  · intro hcore
    rw [hempty] at hcore
    exact (hcore.ne_empty rfl).elim
  · rintro ⟨x⟩
    exact isEmptyElim x

@[simp] theorem extinctionConclusion_end_time :
    (B.extinctionConclusion hempty).end_time = ⊤ := rfl

include B hempty in
theorem continuation_of_core_empty : Nonempty (RepairedBranchContinuationData I) :=
  ⟨⟨B.extinctionConclusion hempty⟩⟩

end PoincareMT.RepairedContinuationLimitBridge
