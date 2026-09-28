import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Nonempty
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Vanishing








set_option autoImplicit false

universe u

namespace PoincareConjecture

namespace SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice₀ slice₁ : ℝ → GeneralizedSliceCarrier.{u}}
    {metric₀ : ∀ t, RiemannianMetric 3 (slice₀ t).carrier}
    {metric₁ : ∀ t, RiemannianMetric 3 (slice₁ t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice₀ metric₀ T)
    (hSlice : ∀ t ∈ Set.Icc 0 T, slice₀ t = slice₁ t)
    (hMetric : ∀ t ∈ Set.Icc 0 T, HEq (metric₀ t) (metric₁ t))


noncomputable def rebuildPast : SurgeryEventData g₀ K P slice₁ metric₁ T :=
  E.copyPast (past := fun t => ⟨slice₀ t, metric₀ t⟩)
    (future := fun t => ⟨slice₁ t, metric₁ t⟩)
    (fun t ht => SurgeryEventRebuild.sliceMetric_eq (hSlice t ht) (hMetric t ht))

@[simp] theorem rebuildPast_tMinus : (E.rebuildPast hSlice hMetric).tMinus = E.tMinus := rfl

@[simp] theorem rebuildPast_terminal :
    (E.rebuildPast hSlice hMetric).terminal = E.terminal := rfl

@[simp] theorem rebuildPast_limit_metric :
    (E.rebuildPast hSlice hMetric).limit_metric = E.limit_metric := rfl

@[simp] theorem rebuildPast_limit_connection :
    (E.rebuildPast hSlice hMetric).limit_connection = E.limit_connection := rfl

@[simp] theorem rebuildPast_cap_count :
    (E.rebuildPast hSlice hMetric).cap_count = E.cap_count := rfl

@[simp] theorem rebuildPast_necks :
    (E.rebuildPast hSlice hMetric).necks = E.necks := rfl

@[simp] theorem rebuildPast_local_result :
    (E.rebuildPast hSlice hMetric).local_result = E.local_result := rfl

theorem rebuildPast_pre_flow_heq :
    HEq (E.rebuildPast hSlice hMetric).pre_flow E.pre_flow :=
  E.copyPast_pre_flow_heq (past := fun t => ⟨slice₀ t, metric₀ t⟩)
    (future := fun t => ⟨slice₁ t, metric₁ t⟩) _

theorem rebuildPast_preservation :
    M33NonemptyEventDataPreservation E (E.rebuildPast hSlice hMetric) :=
  E.copyPast_preservation (past := fun t => ⟨slice₀ t, metric₀ t⟩)
    (future := fun t => ⟨slice₁ t, metric₁ t⟩) _

theorem rebuildPast_retained_image :
    (E.rebuildPast hSlice hMetric).limit_identify.map ''
        (E.rebuildPast hSlice hMetric).retained_pre =
      E.limit_identify.map '' E.retained_pre :=
  eq_of_heq (E.rebuildPast_preservation hSlice hMetric).retained_image_heq


theorem rebuildPast_preservation_of_heq
    {g₁ : StandardInitialMetric} {K₁ : MetricSurgeryConstants} {P₁ : SurgeryParameters}
    (B : SurgeryEventData g₁ K₁ P₁ slice₁ metric₁ T)
    (hg : g₁ = g₀) (hK : K₁ = K) (hP : P₁ = P)
    (hB : HEq B (E.rebuildPast hSlice hMetric)) :
    M33NonemptyEventDataPreservation E B := by
  subst g₁ K₁ P₁
  have heq : B = E.rebuildPast hSlice hMetric := eq_of_heq hB
  subst B
  exact E.rebuildPast_preservation hSlice hMetric

end SurgeryEventData

namespace SurgeryVanishingEventData

variable {P : SurgeryParameters} {slice₀ slice₁ : ℝ → GeneralizedSliceCarrier.{u}}
    {metric₀ : ∀ t, RiemannianMetric 3 (slice₀ t).carrier}
    {metric₁ : ∀ t, RiemannianMetric 3 (slice₁ t).carrier} {T : ℝ}
    (E : SurgeryVanishingEventData P slice₀ metric₀ T)
    (hSlice : ∀ t ∈ Set.Icc 0 T, slice₀ t = slice₁ t)
    (hMetric : ∀ t ∈ Set.Icc 0 T, HEq (metric₀ t) (metric₁ t))


noncomputable def rebuildPast : SurgeryVanishingEventData P slice₁ metric₁ T :=
  E.copyPast (past := fun t => ⟨slice₀ t, metric₀ t⟩)
    (future := fun t => ⟨slice₁ t, metric₁ t⟩)
    (fun t ht => SurgeryEventRebuild.sliceMetric_eq (hSlice t ht) (hMetric t ht))

@[simp] theorem rebuildPast_tMinus : (E.rebuildPast hSlice hMetric).tMinus = E.tMinus := rfl

@[simp] theorem rebuildPast_left_limit_volume :
    (E.rebuildPast hSlice hMetric).left_limit_volume = E.left_limit_volume := rfl

theorem rebuildPast_pre_flow_heq :
    HEq (E.rebuildPast hSlice hMetric).pre_flow E.pre_flow :=
  E.copyPast_pre_flow_heq (past := fun t => ⟨slice₀ t, metric₀ t⟩)
    (future := fun t => ⟨slice₁ t, metric₁ t⟩) _

theorem rebuildPast_preservation :
    M33VanishingEventDataPreservation E (E.rebuildPast hSlice hMetric) :=
  E.copyPast_preservation (past := fun t => ⟨slice₀ t, metric₀ t⟩)
    (future := fun t => ⟨slice₁ t, metric₁ t⟩) _

theorem rebuildPast_preservation_of_heq {P₁ : SurgeryParameters}
    (B : SurgeryVanishingEventData P₁ slice₁ metric₁ T) (hP : P₁ = P)
    (hB : HEq B (E.rebuildPast hSlice hMetric)) :
    M33VanishingEventDataPreservation E B := by
  subst P₁
  have heq : B = E.rebuildPast hSlice hMetric := eq_of_heq hB
  subst B
  exact E.rebuildPast_preservation hSlice hMetric

end SurgeryVanishingEventData

end PoincareConjecture
