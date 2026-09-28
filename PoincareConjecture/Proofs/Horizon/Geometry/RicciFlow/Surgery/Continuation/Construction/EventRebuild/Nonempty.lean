import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.EventPreservation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.SurgeryEventData

open SurgeryEventRebuild

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {past future : ℝ → SliceMetric.{u}} {T : ℝ}


noncomputable def copyPast
    (E : SurgeryEventData g₀ K P (fun t => (past t).1) (fun t => (past t).2) T)
    (hPast : ∀ t ∈ Set.Icc 0 T, past t = future t) :
    SurgeryEventData g₀ K P (fun t => (future t).1) (fun t => (future t).2) T := by
  have hm := hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩
  have hT := hPast T ⟨E.tMinus_nonnegative.trans E.tMinus_lt.le, le_rfl⟩
  refine {
    tMinus := E.tMinus
    tMinus_nonnegative := E.tMinus_nonnegative
    tMinus_lt := E.tMinus_lt
    preterminal_close := E.preterminal_close
    pre_flow := flow hm E.pre_flow
    pre_identify := fun t => diffeomorph hm
      (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩) (E.pre_identify t)
    pre_initial := by
      intro x
      obtain ⟨y, rfl⟩ := (identify (past E.tMinus) (future E.tMinus) hm).surjective x
      exact (diffeomorph_apply hm hm
        (E.pre_identify ⟨E.tMinus, ⟨le_rfl, E.tMinus_lt⟩⟩) y).trans
          (congrArg (identify (past E.tMinus) (future E.tMinus) hm) (E.pre_initial y))
    pre_metric := fun t => diffeomorph_flow_metric_pullback
      hm (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩)
      E.pre_flow t.1 (E.pre_identify t) (E.pre_metric t)
    regular_limit := relabel (C := fun p => Set p.1.carrier) hm E.regular_limit
    regular_limit_eq := ?_
    regular_limit_open := ?_
    terminal := E.terminal
    limit_identify := regionSource hm E.terminal E.regular_limit Set.univ E.limit_identify
    limit_metric := E.limit_metric
    limit_connection := E.limit_connection
    metric_converges := ?_
    retained_pre := relabel (C := fun p => Set p.1.carrier) hm E.retained_pre
    retained_pre_compact := ?_
    retained_pre_subset := ?_
    low_curvature_retained := ?_
    retained_post := relabel (C := fun p => Set p.1.carrier) hT E.retained_post
    retained_post_compact := ?_
    retention := region hm hT E.retained_pre E.retained_post E.retention
    retained_metric := ?_
    cap_count := E.cap_count
    caps := relabel
      (C := fun p => Fin E.cap_count → SurgeryCapChart g₀ p.1 p.2 (P.h T)) hT E.caps
    cap_disjoint := ?_
    post_cover := ?_
    cap_boundary := ?_
    necks := E.necks
    neck_carrier_disjoint := E.neck_carrier_disjoint
    neck_time := E.neck_time
    neck_delta := E.neck_delta
    neck_scale := E.neck_scale
    pre_boundary := ?_
    boundary_correspondence := ?_
    neck_negative_retained := ?_
    neck_positive_discarded := ?_
    local_result := E.local_result
    local_embed := relabel
      (C := fun p => ∀ i, (E.local_result i).output.carrier → p.1.carrier) hT E.local_embed
    local_embed_smooth := ?_
    local_embed_injective := ?_
    local_metric := ?_
    local_tip := ?_
    local_cap_image := ?_
    local_retention := ?_
    disappearing_start := E.disappearing_start
    disappearing_start_bounds := E.disappearing_start_bounds
    disappearing_curvature := ?_
    disappearing_cover := ?_ }
  all_goals
    try dsimp only [flow, diffeomorph, relabel, regionSource, region] at *
    generalize hval : future E.tMinus = m at *
    clear hval
    subst m
    generalize hval : future T = b at *
    clear hval
    subst b
  · exact E.regular_limit_eq
  · exact E.regular_limit_open
  · exact E.metric_converges
  · exact E.retained_pre_compact
  · exact E.retained_pre_subset
  · exact E.low_curvature_retained
  · exact E.retained_post_compact
  · exact E.retained_metric
  · exact E.cap_disjoint
  · exact E.post_cover
  · exact E.cap_boundary
  · exact E.pre_boundary
  · exact E.boundary_correspondence
  · exact E.neck_negative_retained
  · exact E.neck_positive_discarded
  · exact E.local_embed_smooth
  · exact E.local_embed_injective
  · exact E.local_metric
  · exact E.local_tip
  · exact E.local_cap_image
  · exact E.local_retention
  · exact E.disappearing_curvature
  · exact E.disappearing_cover

variable (E : SurgeryEventData g₀ K P (fun t => (past t).1) (fun t => (past t).2) T)
    (hPast : ∀ t ∈ Set.Icc 0 T, past t = future t)

@[simp] theorem copyPast_tMinus : (E.copyPast hPast).tMinus = E.tMinus := rfl

@[simp] theorem copyPast_terminal : (E.copyPast hPast).terminal = E.terminal := rfl

@[simp] theorem copyPast_limit_metric : (E.copyPast hPast).limit_metric = E.limit_metric := rfl

@[simp] theorem copyPast_limit_connection :
    (E.copyPast hPast).limit_connection = E.limit_connection := rfl

@[simp] theorem copyPast_cap_count : (E.copyPast hPast).cap_count = E.cap_count := rfl

@[simp] theorem copyPast_necks : (E.copyPast hPast).necks = E.necks := rfl

@[simp] theorem copyPast_local_result : (E.copyPast hPast).local_result = E.local_result := rfl

theorem copyPast_pre_flow_heq : HEq (E.copyPast hPast).pre_flow E.pre_flow :=
  flow_heq (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩) E.pre_flow

theorem copyPast_pre_identify_apply (t : Set.Ico E.tMinus T)
    (x : (past E.tMinus).1.carrier) :
    (E.copyPast hPast).pre_identify t
      (identify (past E.tMinus) (future E.tMinus)
        (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩) x) =
      identify (past t.1) (future t.1)
        (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩) (E.pre_identify t x) :=
  diffeomorph_apply (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩)
    (hPast t.1 ⟨E.tMinus_nonnegative.trans t.2.1, t.2.2.le⟩) (E.pre_identify t) x

theorem copyPast_retained_pre_image :
    identify (past E.tMinus) (future E.tMinus) (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩) ''
      E.retained_pre = (E.copyPast hPast).retained_pre :=
  relabel_set_image (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩) E.retained_pre

theorem copyPast_retained_post_image :
    identify (past T) (future T) (hPast T ⟨E.tMinus_nonnegative.trans E.tMinus_lt.le, le_rfl⟩) ''
      E.retained_post = (E.copyPast hPast).retained_post :=
  relabel_set_image (hPast T ⟨E.tMinus_nonnegative.trans E.tMinus_lt.le, le_rfl⟩) E.retained_post

theorem copyPast_limit_identify_map (x : (past E.tMinus).1.carrier) :
    (E.copyPast hPast).limit_identify.map
      (identify (past E.tMinus) (future E.tMinus)
        (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩) x) =
        E.limit_identify.map x :=
  regionSource_map (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩)
    E.terminal E.regular_limit Set.univ E.limit_identify x

theorem copyPast_retention_map (x : (past E.tMinus).1.carrier) :
    (E.copyPast hPast).retention.map
      (identify (past E.tMinus) (future E.tMinus)
        (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩) x) =
      identify (past T) (future T)
        (hPast T ⟨E.tMinus_nonnegative.trans E.tMinus_lt.le, le_rfl⟩)
        (E.retention.map x) :=
  region_map (hPast E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩)
    (hPast T ⟨E.tMinus_nonnegative.trans E.tMinus_lt.le, le_rfl⟩)
    E.retained_pre E.retained_post E.retention x


theorem copyPast_preservation : M33NonemptyEventDataPreservation E (E.copyPast hPast) := by
  refine {
    terminal_eq := rfl
    limit_metric_heq := HEq.rfl
    limit_connection_heq := HEq.rfl
    cap_count_eq := rfl
    necks_heq := HEq.rfl
    retained_image_heq := ?_ }
  apply heq_of_eq
  rw [← E.copyPast_retained_pre_image hPast, Set.image_image]
  apply Set.image_congr
  intro x _
  exact E.copyPast_limit_identify_map hPast x

end PoincareConjecture.SurgeryEventData
