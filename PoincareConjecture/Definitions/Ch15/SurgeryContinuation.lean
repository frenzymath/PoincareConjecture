import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure SurgeryPreterminalSlab (F : SurgeryFlowData.{u}) (T : ℝ) where
  start : ℝ
  start_mem : start ∈ F.time_domain
  start_lt : start < T
  start_initial_or_surgery : start = 0 ∨ start ∈ F.surgery_times
  time_subset : Set.Ico start T ⊆ F.time_domain
  surgery_free : Disjoint F.surgery_times (Set.Ioo start T)
  flow : RicciFlow 3 (F.slice start).carrier (Set.Ico start T)
  identify : ∀ t : Set.Ico start T,
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice start).carrier (F.slice t.1).carrier ∞
  initial_identify : ∀ x, identify ⟨start, ⟨le_rfl, start_lt⟩⟩ x = x
  metric_pullback : ∀ t x v w,
    (F.metric t.1).inner (identify t x)
      (mfderiv (𝓡 3) (𝓡 3) (identify t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify t) x w) =
        (flow.metric t.1).inner x v w
  transport_compatibility : ∀ a b hab hJ habs,
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc a b, ∀ ht : t ∈ Set.Icc a b,
    ∀ hs' : s ∈ Set.Ico start T, ∀ ht' : t ∈ Set.Ico start T, ∀ x,
      (F.regular_slabs a b hab hJ habs).transport ⟨s, hs⟩ ⟨t, ht⟩
        (identify ⟨s, hs'⟩ x) = identify ⟨t, ht'⟩ x
  curvature_unbounded : ∀ L : ℝ, ∀ s : ℝ, s < T →
    ∃ t ∈ Set.Ioo (max start s) T, ∃ x : (F.slice start).carrier,
      L < (flow.connection t).curvatureTensorNorm x
  terminal_event : SurgeryEventData F.standard_initial F.local_constants F.parameters
    F.slice F.metric T
  terminal_vanishing_event : SurgeryVanishingEventData F.parameters F.slice F.metric T

structure SurgeryContinuationInput (F : SurgeryFlowData.{u}) (T : ℝ) where
  terminal_pos : 0 < T
  time_domain_eq : F.time_domain = Set.Ico 0 T
  last_slab : SurgeryPreterminalSlab F T
  admissible : SurgeryFlowAdmissible F
  pinched : SurgeryFlowPinched F
  canonical : SurgeryCanonicalAssumption F
  noncollapsed : SurgeryNoncollapsed F

structure SurgeryFlowExtension (F : SurgeryFlowData.{u}) where
  extended : SurgeryFlowData.{u}
  old_times : F.time_domain ⊆ extended.time_domain
  standard_initial_eq : extended.standard_initial = F.standard_initial
  local_constants_eq : extended.local_constants = F.local_constants
  parameters_eq : extended.parameters = F.parameters
  identify : ∀ t ∈ F.time_domain,
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice t).carrier (extended.slice t).carrier ∞
  metric_pullback : ∀ t ht x v w,
    (extended.metric t).inner (identify t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (identify t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify t ht) x w) = (F.metric t).inner x v w
  old_surgery_times : ∀ t ∈ F.time_domain,
    t ∈ extended.surgery_times ↔ t ∈ F.surgery_times
  ordinary_compatibility : ∀ a b hab hJ habs,
    ∀ hJ' : Set.Icc a b ⊆ extended.time_domain,
    ∀ habs' : Disjoint extended.surgery_times (Set.Ioc a b),
    ∀ s t : Set.Icc a b, ∀ x : (F.slice s.1).carrier,
      (extended.regular_slabs a b hab hJ' habs').transport s t
        (identify s.1 (hJ s.2) x) =
          identify t.1 (hJ t.2)
            ((F.regular_slabs a b hab hJ habs).transport s t x)
  old_event_reference : ∀ T hT [Nonempty (F.slice T).carrier]
    [Nonempty (extended.slice T).carrier], ∀ hT' : T ∈ extended.surgery_times,
      (extended.event T hT').tMinus = (F.event T hT).tMinus
  old_retained_post : ∀ T hT hT' [Nonempty (F.slice T).carrier]
    [Nonempty (extended.slice T).carrier],
    identify T (F.surgery_times_subset hT) '' (F.event T hT).retained_post =
      (extended.event T hT').retained_post
  old_retained_pre : ∀ T hT hT' [Nonempty (F.slice T).carrier]
    [Nonempty (extended.slice T).carrier],
    ∀ t : Set.Ico (F.event T hT).tMinus T,
    ∀ ht : t.1 ∈ F.time_domain,
    ∀ ht' : t.1 ∈ Set.Ico (extended.event T hT').tMinus T,
      (fun x => ((extended.event T hT').pre_identify ⟨t.1, ht'⟩).symm
        (identify t.1 ht ((F.event T hT).pre_identify t x))) ''
          (F.event T hT).retained_pre = (extended.event T hT').retained_pre
  old_retention : ∀ T hT hT' [Nonempty (F.slice T).carrier]
    [Nonempty (extended.slice T).carrier],
    ∀ t : Set.Ico (F.event T hT).tMinus T,
    ∀ ht : t.1 ∈ F.time_domain,
    ∀ ht' : t.1 ∈ Set.Ico (extended.event T hT').tMinus T,
    ∀ x ∈ (F.event T hT).retained_pre,
      identify T (F.surgery_times_subset hT) ((F.event T hT).retention.map x) =
        (extended.event T hT').retention.map
          (((extended.event T hT').pre_identify ⟨t.1, ht'⟩).symm
            (identify t.1 ht ((F.event T hT).pre_identify t x)))
  old_vanishing_reference : ∀ T hT [IsEmpty (F.slice T).carrier]
    [IsEmpty (extended.slice T).carrier], ∀ hT' : T ∈ extended.surgery_times,
      (extended.vanishing_event T hT').tMinus = (F.vanishing_event T hT).tMinus

structure SurgeryTerminalNonemptyOperationCertificate
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : SurgeryContinuationInput F T)
    (E : SurgeryFlowExtension F)
    (hT : T ∈ E.extended.surgery_times)
    (hsource : Nonempty (F.slice T).carrier)
    (hpost : Nonempty (E.extended.slice T).carrier) where
  post_identify : Diffeomorph (𝓡 3) (𝓡 3) (F.slice T).carrier
    (E.extended.slice T).carrier ∞
  post_metric_pullback : ∀ x v w,
    (E.extended.metric T).inner (post_identify x)
      (mfderiv (𝓡 3) (𝓡 3) post_identify x v)
      (mfderiv (𝓡 3) (𝓡 3) post_identify x w) =
        (F.metric T).inner x v w
  source_tMinus_eq_start : I.last_slab.terminal_event.tMinus = I.last_slab.start
  source_tMinus_mem : I.last_slab.terminal_event.tMinus ∈ F.time_domain
  source_pre_flow_eq : HEq I.last_slab.terminal_event.pre_flow I.last_slab.flow
  source_pre_identify_eq : HEq I.last_slab.terminal_event.pre_identify I.last_slab.identify
  source_vanishing_tMinus_eq_start :
    I.last_slab.terminal_vanishing_event.tMinus = I.last_slab.start
  source_vanishing_pre_flow_eq :
    HEq I.last_slab.terminal_vanishing_event.pre_flow I.last_slab.flow
  source_vanishing_pre_identify_eq :
    HEq I.last_slab.terminal_vanishing_event.pre_identify I.last_slab.identify
  event_tMinus_eq_source : ∀ [Nonempty (E.extended.slice T).carrier],
    (E.extended.event T hT).tMinus = I.last_slab.terminal_event.tMinus
  event_pre_flow_eq_source : ∀ [Nonempty (E.extended.slice T).carrier],
    HEq (E.extended.event T hT).pre_flow I.last_slab.terminal_event.pre_flow
  event_pre_identify_eq_source : ∀ [Nonempty (E.extended.slice T).carrier],
    HEq (E.extended.event T hT).pre_identify
      I.last_slab.terminal_event.pre_identify
  retained_post_transport : ∀ [Nonempty (E.extended.slice T).carrier],
    post_identify '' I.last_slab.terminal_event.retained_post =
      (E.extended.event T hT).retained_post
  retained_pre_transport : ∀ [Nonempty (E.extended.slice T).carrier],
    HEq (E.identify I.last_slab.terminal_event.tMinus source_tMinus_mem ''
        I.last_slab.terminal_event.retained_pre)
      ((E.extended.event T hT).retained_pre)

  cap_count_eq : I.last_slab.terminal_event.cap_count =
    (E.extended.event T hT).cap_count
  limit_identify : Diffeomorph (𝓡 3) (𝓡 3)
    I.last_slab.terminal_event.terminal.carrier
    (E.extended.event T hT).terminal.carrier ∞
  limit_metric_pullback : ∀ x v w,
    (E.extended.event T hT).limit_metric.inner (limit_identify x)
      (mfderiv (𝓡 3) (𝓡 3) limit_identify x v)
      (mfderiv (𝓡 3) (𝓡 3) limit_identify x w) =
        I.last_slab.terminal_event.limit_metric.inner x v w
  neck_carrier_transport : ∀ i : Fin I.last_slab.terminal_event.cap_count,
    limit_identify '' (I.last_slab.terminal_event.necks i).neck.carrier =
      ((E.extended.event T hT).necks (Fin.cast cap_count_eq i)).neck.carrier
  cap_carrier_transport : ∀ i : Fin I.last_slab.terminal_event.cap_count,
    post_identify '' (I.last_slab.terminal_event.caps i).carrier =
      ((E.extended.event T hT).caps (Fin.cast cap_count_eq i)).carrier
  local_result_output_identify : ∀ i : Fin I.last_slab.terminal_event.cap_count,
    Diffeomorph (𝓡 3) (𝓡 3)
      (I.last_slab.terminal_event.local_result i).output.carrier
      ((E.extended.event T hT).local_result (Fin.cast cap_count_eq i)).output.carrier ∞
  local_result_collapse_transport : ∀ i : Fin I.last_slab.terminal_event.cap_count,
    ∀ x : I.last_slab.terminal_event.terminal.carrier,
      post_identify
          (I.last_slab.terminal_event.local_embed i
            ((I.last_slab.terminal_event.local_result i).collapse x)) =
        (E.extended.event T hT).local_embed (Fin.cast cap_count_eq i)
          (((E.extended.event T hT).local_result (Fin.cast cap_count_eq i)).collapse
            (limit_identify x)
          )
  boundary_transport : ∀ i : Fin I.last_slab.terminal_event.cap_count,
    post_identify '' (I.last_slab.terminal_event.retained_post ∩
      (I.last_slab.terminal_event.caps i).carrier) =
      (E.extended.event T hT).retained_post ∩
        ((E.extended.event T hT).caps (Fin.cast cap_count_eq i)).carrier
  disappearing_start_eq : I.last_slab.terminal_event.disappearing_start =
    (E.extended.event T hT).disappearing_start
  disappearing_cover_transport :
    HEq I.last_slab.terminal_event.disappearing_cover
      (E.extended.event T hT).disappearing_cover

structure SurgeryTerminalVanishingOperationCertificate
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : SurgeryContinuationInput F T)
    (E : SurgeryFlowExtension F)
    (hT : T ∈ E.extended.surgery_times)
    (hsource : IsEmpty (F.slice T).carrier)
    (hempty : IsEmpty (E.extended.slice T).carrier) where
  source_tMinus_eq_start : I.last_slab.terminal_vanishing_event.tMinus = I.last_slab.start
  source_tMinus_mem : I.last_slab.terminal_vanishing_event.tMinus ∈ F.time_domain
  source_pre_flow_eq : HEq I.last_slab.terminal_vanishing_event.pre_flow I.last_slab.flow
  source_pre_identify_eq :
    HEq I.last_slab.terminal_vanishing_event.pre_identify I.last_slab.identify
  vanishing_tMinus_eq_source :
    (E.extended.vanishing_event T hT).tMinus =
      I.last_slab.terminal_vanishing_event.tMinus
  vanishing_pre_flow_eq_source :
    HEq (E.extended.vanishing_event T hT).pre_flow
      I.last_slab.terminal_vanishing_event.pre_flow
  vanishing_pre_identify_eq_source :
    HEq (E.extended.vanishing_event T hT).pre_identify
      I.last_slab.terminal_vanishing_event.pre_identify
  disappearing_start_eq :
    I.last_slab.terminal_vanishing_event.disappearing_start =
      (E.extended.vanishing_event T hT).disappearing_start
  disappearing_cover_transport :
    HEq I.last_slab.terminal_vanishing_event.disappearing_cover
      (E.extended.vanishing_event T hT).disappearing_cover

structure SurgeryContinuationScales (K : MetricSurgeryConstants) where
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le : epsilon₀ ≤ 1 / 200
  C₀ : ℝ → ℝ
  C₀_pos : ∀ epsilon : ℝ, 0 < epsilon → 0 < C₀ epsilon
  delta₀ : ℝ → ℝ → ℝ
  delta₀_pos : ∀ epsilon C : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    C₀ epsilon ≤ C → 0 < delta₀ epsilon C
  delta₀_le : ∀ epsilon C : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    C₀ epsilon ≤ C → delta₀ epsilon C ≤ min K.delta₀ (epsilon / 6)
  h : ℝ → ℝ → ℝ → ℝ → ℝ
  h_pos : ∀ epsilon C r delta : ℝ,
    0 < epsilon → epsilon ≤ epsilon₀ → C₀ epsilon ≤ C → 0 < r →
    0 < delta → delta ≤ delta₀ epsilon C → 0 < h epsilon C r delta
  h_bound : ∀ epsilon C r delta : ℝ,
    0 < epsilon → epsilon ≤ epsilon₀ → C₀ epsilon ≤ C → 0 < r →
    0 < delta → delta ≤ delta₀ epsilon C →
      h epsilon C r delta ≤ min (delta ^ 2 * r) (K.R₀ ^ (-1 / 2 : ℝ))

structure SurgeryContinuationConclusion {F : SurgeryFlowData.{u}}
    {T : ℝ} (I : SurgeryContinuationInput F T) where
  extension : SurgeryFlowExtension F
  end_time : ℝ≥0∞
  extends_past : ENNReal.ofReal T < end_time
  time_domain_eq : extension.extended.time_domain =
    {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < end_time}
  surgery_at_terminal : T ∈ extension.extended.surgery_times
  terminal_operation :
    (∃ hsource : Nonempty (F.slice T).carrier,
      ∃ hpost : Nonempty (extension.extended.slice T).carrier,
      Nonempty (SurgeryTerminalNonemptyOperationCertificate I extension
        surgery_at_terminal hsource hpost)) ∨
    (∃ hsource : IsEmpty (F.slice T).carrier,
      ∃ hempty : IsEmpty (extension.extended.slice T).carrier,
      Nonempty (SurgeryTerminalVanishingOperationCertificate I extension
        surgery_at_terminal hsource hempty))
  post_terminal_interval : ∃ d : ℝ, 0 < d ∧
    Set.Ioo T (T + d) ⊆ extension.extended.time_domain ∧
    Disjoint extension.extended.surgery_times (Set.Ioo T (T + d))
  admissible : SurgeryFlowAdmissible extension.extended
  pinched : SurgeryFlowPinched extension.extended
  canonical : SurgeryCanonicalAssumption extension.extended
  noncollapsed : SurgeryNoncollapsed extension.extended
  terminal_reference_after : ∀ [Nonempty (extension.extended.slice T).carrier],
    I.last_slab.start ≤ (extension.extended.event T surgery_at_terminal).tMinus
  terminal_vanishing_reference_after : ∀ [IsEmpty (extension.extended.slice T).carrier],
    I.last_slab.start ≤ (extension.extended.vanishing_event T surgery_at_terminal).tMinus

end PoincareConjecture
