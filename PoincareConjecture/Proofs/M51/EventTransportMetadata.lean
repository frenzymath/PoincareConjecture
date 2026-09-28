import PoincareConjecture.Proofs.M51.EventTransportPolicy
import PoincareConjecture.Proofs.M51.VanishingTransport

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.SurgeryEventData

variable {g₀ g₁ : StandardInitialMetric} {K₀ K₁ : MetricSurgeryConstants}
  {P₀ P₁ : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K₀ P₀ slice metric T)
  (hg : g₀ = g₁) (hK : K₀ = K₁) (hP : P₀ = P₁)

def castMetadata : SurgeryEventData g₁ K₁ P₁ slice metric T where
  tMinus := E.tMinus
  tMinus_nonnegative := E.tMinus_nonnegative
  tMinus_lt := E.tMinus_lt
  preterminal_close := by subst P₁; exact E.preterminal_close
  pre_flow := E.pre_flow
  pre_identify := E.pre_identify
  pre_initial := E.pre_initial
  pre_metric := E.pre_metric
  regular_limit := E.regular_limit
  regular_limit_eq := E.regular_limit_eq
  regular_limit_open := E.regular_limit_open
  terminal := E.terminal
  limit_identify := E.limit_identify
  limit_metric := E.limit_metric
  limit_connection := E.limit_connection
  metric_converges := E.metric_converges
  retained_pre := E.retained_pre
  retained_pre_compact := E.retained_pre_compact
  retained_pre_subset := E.retained_pre_subset
  low_curvature_retained := by subst P₁; exact E.low_curvature_retained
  retained_post := E.retained_post
  retained_post_compact := E.retained_post_compact
  retention := E.retention
  retained_metric := E.retained_metric
  cap_count := E.cap_count
  caps := by subst g₁; subst P₁; exact E.caps
  cap_disjoint := by subst g₁; subst P₁; exact E.cap_disjoint
  post_cover := by subst g₁; subst P₁; exact E.post_cover
  cap_boundary := by subst g₁; subst P₁; exact E.cap_boundary
  necks i := {
    neck := (E.necks i).neck
    time := (E.necks i).time
    delta_le := by subst K₁; exact (E.necks i).delta_le
    scalar_large := by subst K₁; exact (E.necks i).scalar_large
    pinched := (E.necks i).pinched }
  neck_carrier_disjoint := by subst K₁; exact E.neck_carrier_disjoint
  neck_time := by subst K₁; exact E.neck_time
  neck_delta := by subst K₁; subst P₁; exact E.neck_delta
  neck_scale := by subst K₁; subst P₁; exact E.neck_scale
  pre_boundary := by subst K₁; exact E.pre_boundary
  boundary_correspondence := by
    subst g₁; subst K₁; subst P₁; exact E.boundary_correspondence
  neck_negative_retained := by subst K₁; exact E.neck_negative_retained
  neck_positive_discarded := by subst K₁; exact E.neck_positive_discarded
  local_result := by subst g₁; subst K₁; exact E.local_result
  local_embed := by subst g₁; subst K₁; exact E.local_embed
  local_embed_smooth := by subst g₁; subst K₁; exact E.local_embed_smooth
  local_embed_injective := by subst g₁; subst K₁; exact E.local_embed_injective
  local_metric := by subst g₁; subst K₁; exact E.local_metric
  local_tip := by subst g₁; subst K₁; subst P₁; exact E.local_tip
  local_cap_image := by subst g₁; subst K₁; subst P₁; exact E.local_cap_image
  local_retention := by subst g₁; subst K₁; exact E.local_retention
  disappearing_start := E.disappearing_start
  disappearing_start_bounds := E.disappearing_start_bounds
  disappearing_curvature := by subst P₁; exact E.disappearing_curvature
  disappearing_cover := by subst P₁; exact E.disappearing_cover

theorem castMetadata_heq : HEq (E.castMetadata hg hK hP) E := by
  subst g₁
  subst K₁
  subst P₁
  rfl

@[simp] theorem castMetadata_tMinus :
    (E.castMetadata hg hK hP).tMinus = E.tMinus := by
  subst g₁
  subst K₁
  subst P₁
  rfl

@[simp] theorem castMetadata_terminal :
    (E.castMetadata hg hK hP).terminal = E.terminal := by
  subst g₁
  subst K₁
  subst P₁
  rfl

@[simp] theorem castMetadata_cap_count :
    (E.castMetadata hg hK hP).cap_count = E.cap_count := by
  subst g₁
  subst K₁
  subst P₁
  rfl

@[simp] theorem castMetadata_disappearing_start :
    (E.castMetadata hg hK hP).disappearing_start = E.disappearing_start := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_pre_flow : HEq (E.castMetadata hg hK hP).pre_flow E.pre_flow := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_pre_identify :
    HEq (E.castMetadata hg hK hP).pre_identify E.pre_identify := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_regular_limit :
    HEq (E.castMetadata hg hK hP).regular_limit E.regular_limit := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_retained_pre :
    HEq (E.castMetadata hg hK hP).retained_pre E.retained_pre := by
  subst g₁
  subst K₁
  subst P₁
  rfl

@[simp] theorem castMetadata_retained_post :
    (E.castMetadata hg hK hP).retained_post = E.retained_post := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_retention :
    HEq (E.castMetadata hg hK hP).retention E.retention := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_limit_identify :
    HEq (E.castMetadata hg hK hP).limit_identify E.limit_identify := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_limit_metric :
    HEq (E.castMetadata hg hK hP).limit_metric E.limit_metric := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_limit_connection :
    HEq (E.castMetadata hg hK hP).limit_connection E.limit_connection := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_necks : HEq (E.castMetadata hg hK hP).necks E.necks := by
  subst g₁
  subst K₁
  subst P₁
  rfl

@[simp] theorem castMetadata_neck (i : Fin E.cap_count) :
    ((E.castMetadata hg hK hP).necks i).neck = (E.necks i).neck := rfl

theorem castMetadata_local_result :
    HEq (E.castMetadata hg hK hP).local_result E.local_result := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_local_embed :
    HEq (E.castMetadata hg hK hP).local_embed E.local_embed := by
  subst g₁
  subst K₁
  subst P₁
  rfl

theorem castMetadata_policy (hE : Nonempty (SurgeryEventTerminalPolicy E)) :
    Nonempty (SurgeryEventTerminalPolicy (E.castMetadata hg hK hP)) := by
  subst g₁
  subst K₁
  subst P₁
  exact hE

end PoincareConjecture.SurgeryEventData

namespace PoincareConjecture.SurgeryVanishingEventData

variable {P₀ P₁ : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  (E : SurgeryVanishingEventData P₀ slice metric T) (hP : P₀ = P₁)

def castParameters : SurgeryVanishingEventData P₁ slice metric T where
  tMinus := E.tMinus
  tMinus_nonnegative := E.tMinus_nonnegative
  tMinus_lt := E.tMinus_lt
  pre_nonempty := E.pre_nonempty
  pre_flow := E.pre_flow
  pre_identify := E.pre_identify
  pre_initial := E.pre_initial
  pre_metric := E.pre_metric
  left_limit_volume := E.left_limit_volume
  left_limit_volume_tendsto := E.left_limit_volume_tendsto
  disappearing_start := E.disappearing_start
  disappearing_start_bounds := E.disappearing_start_bounds
  disappearing_curvature := by subst P₁; exact E.disappearing_curvature
  disappearing_cover := by subst P₁; exact E.disappearing_cover

theorem castParameters_heq : HEq (E.castParameters hP) E := by
  subst P₁
  rfl

@[simp] theorem castParameters_tMinus :
    (E.castParameters hP).tMinus = E.tMinus := by
  subst P₁
  rfl

@[simp] theorem castParameters_disappearing_start :
    (E.castParameters hP).disappearing_start = E.disappearing_start := by
  subst P₁
  rfl

@[simp] theorem castParameters_left_limit_volume :
    (E.castParameters hP).left_limit_volume = E.left_limit_volume := by
  subst P₁
  rfl

theorem castParameters_pre_flow : HEq (E.castParameters hP).pre_flow E.pre_flow := by
  subst P₁
  rfl

theorem castParameters_pre_identify :
    HEq (E.castParameters hP).pre_identify E.pre_identify := by
  subst P₁
  rfl

theorem castParameters_policy
    (hE : SurgeryVanishingEventTerminalPolicy E) :
    SurgeryVanishingEventTerminalPolicy (E.castParameters hP) := by
  subst P₁
  exact hE

end PoincareConjecture.SurgeryVanishingEventData
