import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

namespace M51EventCopy

def relabel {C : ℝ → Sort v} {s t : ℝ} (h : s = t) (x : C s) : C t := h ▸ x

theorem relabel_heq {C : ℝ → Sort v} {s t : ℝ} (h : s = t) (x : C s) :
    HEq (relabel h x) x := by
  subst t
  rfl

noncomputable def timeEquivalence (slice : ℝ → GeneralizedSliceCarrier.{u})
    (s t : ℝ) (h : s = t) :
    Diffeomorph (𝓡 3) (𝓡 3) (slice s).carrier (slice t).carrier ∞ := by
  subst t
  exact Diffeomorph.refl (𝓡 3) (slice s).carrier ∞

noncomputable def identify (slice : ℝ → GeneralizedSliceCarrier.{u})
    (tau : ℝ → ℝ) (t : ℝ) (h : tau t = t) :
    Diffeomorph (𝓡 3) (𝓡 3) (slice t).carrier (slice (tau t)).carrier ∞ :=
  timeEquivalence slice t (tau t) h.symm

theorem relabel_set_image (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s t : ℝ} (h : s = t) (U : Set (slice s).carrier) :
    timeEquivalence slice s t h '' U =
      relabel (C := fun r => Set (slice r).carrier) h U := by
  subst t
  exact Set.image_id _

theorem relabel_map_apply (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s t : ℝ} (h : s = t) {ι : Type*} {A : ι → Type*}
    (f : ∀ i, A i → (slice s).carrier) (i : ι) (x : A i) :
    relabel (C := fun r => ∀ i, A i → (slice r).carrier) h f i x =
      timeEquivalence slice s t h (f i x) := by
  subst t
  rfl

def regionSource (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s t : ℝ} (h : s = t) (B : GeneralizedSliceCarrier.{u})
    (U : Set (slice s).carrier) (V : Set B.carrier)
    (e : SurgeryRegionEquivalence (slice s) B U V) :
    SurgeryRegionEquivalence (slice t) B
      (relabel (C := fun r => Set (slice r).carrier) h U) V := by
  subst t
  exact e

theorem regionSource_map (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s t : ℝ} (h : s = t) (B : GeneralizedSliceCarrier.{u})
    (U : Set (slice s).carrier) (V : Set B.carrier)
    (e : SurgeryRegionEquivalence (slice s) B U V) (x : (slice s).carrier) :
    (regionSource slice h B U V e).map (timeEquivalence slice s t h x) = e.map x := by
  subst t
  rfl

theorem regionSource_inverse (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s t : ℝ} (h : s = t) (B : GeneralizedSliceCarrier.{u})
    (U : Set (slice s).carrier) (V : Set B.carrier)
    (e : SurgeryRegionEquivalence (slice s) B U V) (x : B.carrier) :
    (regionSource slice h B U V e).inverse x =
      timeEquivalence slice s t h (e.inverse x) := by
  subst t
  rfl

def region (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s s' t t' : ℝ} (hs : s = s') (ht : t = t')
    (U : Set (slice s).carrier) (V : Set (slice t).carrier)
    (e : SurgeryRegionEquivalence (slice s) (slice t) U V) :
    SurgeryRegionEquivalence (slice s') (slice t')
      (relabel (C := fun r => Set (slice r).carrier) hs U)
      (relabel (C := fun r => Set (slice r).carrier) ht V) := by
  subst s'
  subst t'
  exact e

theorem region_map (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s s' t t' : ℝ} (hs : s = s') (ht : t = t')
    (U : Set (slice s).carrier) (V : Set (slice t).carrier)
    (e : SurgeryRegionEquivalence (slice s) (slice t) U V) (x : (slice s).carrier) :
    (region slice hs ht U V e).map (timeEquivalence slice s s' hs x) =
      timeEquivalence slice t t' ht (e.map x) := by
  subst s'
  subst t'
  rfl

theorem region_inverse (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s s' t t' : ℝ} (hs : s = s') (ht : t = t')
    (U : Set (slice s).carrier) (V : Set (slice t).carrier)
    (e : SurgeryRegionEquivalence (slice s) (slice t) U V) (x : (slice t).carrier) :
    (region slice hs ht U V e).inverse (timeEquivalence slice t t' ht x) =
      timeEquivalence slice s s' hs (e.inverse x) := by
  subst s'
  subst t'
  rfl

theorem timeEquivalence_apply_heq (slice : ℝ → GeneralizedSliceCarrier.{u})
    (s t : ℝ) (h : s = t) (x : (slice s).carrier) :
    HEq (timeEquivalence slice s t h x) x := by
  subst t
  rfl

theorem identify_apply_heq (slice : ℝ → GeneralizedSliceCarrier.{u})
    (tau : ℝ → ℝ) (t : ℝ) (h : tau t = t) (x : (slice t).carrier) :
    HEq (identify slice tau t h x) x :=
  timeEquivalence_apply_heq slice t (tau t) h.symm x

theorem timeEquivalence_symm_apply_heq (slice : ℝ → GeneralizedSliceCarrier.{u})
    (s t : ℝ) (h : s = t) (x : (slice t).carrier) :
    HEq ((timeEquivalence slice s t h).symm x) x := by
  subst t
  rfl

theorem identify_symm_apply_heq (slice : ℝ → GeneralizedSliceCarrier.{u})
    (tau : ℝ → ℝ) (t : ℝ) (h : tau t = t) (x : (slice (tau t)).carrier) :
    HEq ((identify slice tau t h).symm x) x :=
  timeEquivalence_symm_apply_heq slice t (tau t) h.symm x

noncomputable def diffeomorph (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s s' t t' : ℝ} (hs : s = s') (ht : t = t')
    (f : Diffeomorph (𝓡 3) (𝓡 3) (slice s).carrier (slice t).carrier ∞) :
    Diffeomorph (𝓡 3) (𝓡 3) (slice s').carrier (slice t').carrier ∞ := by
  subst s'
  subst t'
  exact f

theorem diffeomorph_apply (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s s' t t' : ℝ} (hs : s = s') (ht : t = t')
    (f : Diffeomorph (𝓡 3) (𝓡 3) (slice s).carrier (slice t).carrier ∞)
    (x : (slice s).carrier) :
    diffeomorph slice hs ht f (timeEquivalence slice s s' hs x) =
      timeEquivalence slice t t' ht (f x) := by
  subst s'
  subst t'
  rfl

noncomputable def flow (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s t : ℝ} (h : s = t) {J : Set ℝ}
    (B : RicciFlow 3 (slice s).carrier J) : RicciFlow 3 (slice t).carrier J :=
  h ▸ B

theorem flow_heq (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s t : ℝ} (h : s = t) {J : Set ℝ} (B : RicciFlow 3 (slice s).carrier J) :
    HEq (flow slice h B) B := by
  subst t
  rfl

theorem flow_metric_pullback (slice : ℝ → GeneralizedSliceCarrier.{u})
    {s t : ℝ} (h : s = t) {J : Set ℝ} (B : RicciFlow 3 (slice s).carrier J)
    (r : ℝ) (x : (slice s).carrier) (v w : TangentSpace (𝓡 3) x) :
    ((flow slice h B).metric r).inner (timeEquivalence slice s t h x)
      (mfderiv (𝓡 3) (𝓡 3) (timeEquivalence slice s t h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (timeEquivalence slice s t h) x w) =
        (B.metric r).inner x v w := by
  subst t
  change (B.metric r).inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
    (mfderiv (𝓡 3) (𝓡 3) id x w) = _
  rw [mfderiv_id]
  rfl

theorem diffeomorph_flow_metric_pullback
    (slice : ℝ → GeneralizedSliceCarrier.{u})
    (metric : ∀ t, RiemannianMetric 3 (slice t).carrier)
    {s s' t t' : ℝ} (hs : s = s') (ht : t = t') {J : Set ℝ}
    (B : RicciFlow 3 (slice s).carrier J) (r : ℝ)
    (f : Diffeomorph (𝓡 3) (𝓡 3) (slice s).carrier (slice t).carrier ∞)
    (h : ∀ x v w, (metric t).inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
        (B.metric r).inner x v w) :
    ∀ x v w, (metric t').inner (diffeomorph slice hs ht f x)
      (mfderiv (𝓡 3) (𝓡 3) (diffeomorph slice hs ht f) x v)
      (mfderiv (𝓡 3) (𝓡 3) (diffeomorph slice hs ht f) x w) =
        ((flow slice hs B).metric r).inner x v w := by
  subst s'
  subst t'
  exact h

theorem timeEquivalence_metric_pullback
    (slice : ℝ → GeneralizedSliceCarrier.{u})
    (metric : ∀ t, RiemannianMetric 3 (slice t).carrier)
    (s t : ℝ) (h : s = t) (x : (slice s).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (metric t).inner (timeEquivalence slice s t h x)
      (mfderiv (𝓡 3) (𝓡 3) (timeEquivalence slice s t h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (timeEquivalence slice s t h) x w) =
        (metric s).inner x v w := by
  subst t
  change (metric s).inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
    (mfderiv (𝓡 3) (𝓡 3) id x w) = _
  rw [mfderiv_id]
  rfl

theorem identify_metric_pullback (slice : ℝ → GeneralizedSliceCarrier.{u})
    (metric : ∀ t, RiemannianMetric 3 (slice t).carrier)
    (tau : ℝ → ℝ) (t : ℝ) (h : tau t = t) (x : (slice t).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (metric (tau t)).inner (identify slice tau t h x)
      (mfderiv (𝓡 3) (𝓡 3) (identify slice tau t h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify slice tau t h) x w) =
        (metric t).inner x v w :=
  timeEquivalence_metric_pullback slice metric t (tau t) h.symm x v w

end M51EventCopy

namespace SurgeryEventData

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

noncomputable def reindexPast (E : SurgeryEventData g₀ K P slice metric T)
    (tau : ℝ → ℝ) (hTau : ∀ t ≤ T, tau t = t) :
    SurgeryEventData g₀ K P (fun t => slice (tau t)) (fun t => metric (tau t)) T := by
  have hm := hTau E.tMinus E.tMinus_lt.le
  have hT := hTau T le_rfl
  refine {
    tMinus := E.tMinus
    tMinus_nonnegative := E.tMinus_nonnegative
    tMinus_lt := E.tMinus_lt
    preterminal_close := E.preterminal_close
    pre_flow := M51EventCopy.flow slice hm.symm E.pre_flow
    pre_identify := fun t => M51EventCopy.diffeomorph slice hm.symm
      (hTau t.1 t.2.2.le).symm (E.pre_identify t)
    pre_initial := by
      intro x
      obtain ⟨y, rfl⟩ := (M51EventCopy.timeEquivalence slice E.tMinus
        (tau E.tMinus) hm.symm).surjective x
      exact (M51EventCopy.diffeomorph_apply slice hm.symm hm.symm
        (E.pre_identify ⟨E.tMinus, ⟨le_rfl, E.tMinus_lt⟩⟩) y).trans
          (congrArg (M51EventCopy.timeEquivalence slice E.tMinus
            (tau E.tMinus) hm.symm) (E.pre_initial y))
    pre_metric := fun t => M51EventCopy.diffeomorph_flow_metric_pullback slice metric
      hm.symm (hTau t.1 t.2.2.le).symm E.pre_flow t.1
      (E.pre_identify t) (E.pre_metric t)
    regular_limit := M51EventCopy.relabel (C := fun t => Set (slice t).carrier)
      hm.symm E.regular_limit
    regular_limit_eq := ?_
    regular_limit_open := ?_
    terminal := E.terminal
    limit_identify := M51EventCopy.regionSource slice hm.symm E.terminal
      E.regular_limit Set.univ E.limit_identify
    limit_metric := E.limit_metric
    limit_connection := E.limit_connection
    metric_converges := ?_
    retained_pre := M51EventCopy.relabel (C := fun t => Set (slice t).carrier)
      hm.symm E.retained_pre
    retained_pre_compact := ?_
    retained_pre_subset := ?_
    low_curvature_retained := ?_
    retained_post := M51EventCopy.relabel (C := fun t => Set (slice t).carrier)
      hT.symm E.retained_post
    retained_post_compact := ?_
    retention := M51EventCopy.region slice hm.symm hT.symm
      E.retained_pre E.retained_post E.retention
    retained_metric := ?_
    cap_count := E.cap_count
    caps := M51EventCopy.relabel
      (C := fun t => Fin E.cap_count → SurgeryCapChart g₀ (slice t) (metric t) (P.h T))
      hT.symm E.caps
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
    local_embed := M51EventCopy.relabel
      (C := fun t => ∀ i, (E.local_result i).output.carrier → (slice t).carrier)
      hT.symm E.local_embed
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
    try dsimp only [M51EventCopy.flow, M51EventCopy.diffeomorph,
      M51EventCopy.relabel, M51EventCopy.regionSource, M51EventCopy.region] at *
    generalize hval : tau E.tMinus = m at *
    clear hval
    subst m
    generalize hval : tau T = b at *
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

variable (E : SurgeryEventData g₀ K P slice metric T)
    (tau : ℝ → ℝ) (hTau : ∀ t ≤ T, tau t = t)

@[simp] theorem reindexPast_tMinus : (E.reindexPast tau hTau).tMinus = E.tMinus := rfl

@[simp] theorem reindexPast_disappearing_start :
    (E.reindexPast tau hTau).disappearing_start = E.disappearing_start := rfl

@[simp] theorem reindexPast_terminal :
    (E.reindexPast tau hTau).terminal = E.terminal := rfl

@[simp] theorem reindexPast_limit_metric :
    (E.reindexPast tau hTau).limit_metric = E.limit_metric := rfl

@[simp] theorem reindexPast_limit_connection :
    (E.reindexPast tau hTau).limit_connection = E.limit_connection := rfl

@[simp] theorem reindexPast_cap_count :
    (E.reindexPast tau hTau).cap_count = E.cap_count := rfl

@[simp] theorem reindexPast_necks : (E.reindexPast tau hTau).necks = E.necks := rfl

@[simp] theorem reindexPast_local_result :
    (E.reindexPast tau hTau).local_result = E.local_result := rfl

theorem reindexPast_pre_flow_heq : HEq (E.reindexPast tau hTau).pre_flow E.pre_flow :=
  M51EventCopy.flow_heq slice (hTau E.tMinus E.tMinus_lt.le).symm E.pre_flow

theorem reindexPast_pre_identify_apply (t : Set.Ico E.tMinus T)
    (x : (slice E.tMinus).carrier) :
    (E.reindexPast tau hTau).pre_identify t
      (M51EventCopy.identify slice tau E.tMinus (hTau E.tMinus E.tMinus_lt.le) x) =
        M51EventCopy.identify slice tau t.1 (hTau t.1 t.2.2.le) (E.pre_identify t x) :=
  M51EventCopy.diffeomorph_apply slice (hTau E.tMinus E.tMinus_lt.le).symm
    (hTau t.1 t.2.2.le).symm (E.pre_identify t) x

theorem reindexPast_regular_limit_image :
    M51EventCopy.identify slice tau E.tMinus (hTau E.tMinus E.tMinus_lt.le) ''
      E.regular_limit = (E.reindexPast tau hTau).regular_limit :=
  M51EventCopy.relabel_set_image slice (hTau E.tMinus E.tMinus_lt.le).symm E.regular_limit

theorem reindexPast_retained_pre_image :
    M51EventCopy.identify slice tau E.tMinus (hTau E.tMinus E.tMinus_lt.le) ''
      E.retained_pre = (E.reindexPast tau hTau).retained_pre :=
  M51EventCopy.relabel_set_image slice (hTau E.tMinus E.tMinus_lt.le).symm E.retained_pre

theorem reindexPast_retained_post_image :
    M51EventCopy.identify slice tau T (hTau T le_rfl) ''
      E.retained_post = (E.reindexPast tau hTau).retained_post :=
  M51EventCopy.relabel_set_image slice (hTau T le_rfl).symm E.retained_post

theorem reindexPast_limit_identify_map (x : (slice E.tMinus).carrier) :
    (E.reindexPast tau hTau).limit_identify.map
      (M51EventCopy.identify slice tau E.tMinus (hTau E.tMinus E.tMinus_lt.le) x) =
        E.limit_identify.map x :=
  M51EventCopy.regionSource_map slice (hTau E.tMinus E.tMinus_lt.le).symm
    E.terminal E.regular_limit Set.univ E.limit_identify x

theorem reindexPast_limit_identify_inverse (x : E.terminal.carrier) :
    (E.reindexPast tau hTau).limit_identify.inverse x =
      M51EventCopy.identify slice tau E.tMinus (hTau E.tMinus E.tMinus_lt.le)
        (E.limit_identify.inverse x) :=
  M51EventCopy.regionSource_inverse slice (hTau E.tMinus E.tMinus_lt.le).symm
    E.terminal E.regular_limit Set.univ E.limit_identify x

theorem reindexPast_retention_map (x : (slice E.tMinus).carrier) :
    (E.reindexPast tau hTau).retention.map
      (M51EventCopy.identify slice tau E.tMinus (hTau E.tMinus E.tMinus_lt.le) x) =
        M51EventCopy.identify slice tau T (hTau T le_rfl) (E.retention.map x) :=
  M51EventCopy.region_map slice (hTau E.tMinus E.tMinus_lt.le).symm
    (hTau T le_rfl).symm E.retained_pre E.retained_post E.retention x

theorem reindexPast_retention_inverse (x : (slice T).carrier) :
    (E.reindexPast tau hTau).retention.inverse
      (M51EventCopy.identify slice tau T (hTau T le_rfl) x) =
        M51EventCopy.identify slice tau E.tMinus (hTau E.tMinus E.tMinus_lt.le)
          (E.retention.inverse x) :=
  M51EventCopy.region_inverse slice (hTau E.tMinus E.tMinus_lt.le).symm
    (hTau T le_rfl).symm E.retained_pre E.retained_post E.retention x

theorem reindexPast_caps_heq : HEq (E.reindexPast tau hTau).caps E.caps :=
  M51EventCopy.relabel_heq
    (C := fun t => Fin E.cap_count → SurgeryCapChart g₀ (slice t) (metric t) (P.h T))
    (hTau T le_rfl).symm E.caps

theorem reindexPast_local_embed_apply (i : Fin E.cap_count)
    (x : (E.local_result i).output.carrier) :
    (E.reindexPast tau hTau).local_embed i x =
      M51EventCopy.identify slice tau T (hTau T le_rfl) (E.local_embed i x) :=
  M51EventCopy.relabel_map_apply slice (hTau T le_rfl).symm E.local_embed i x

end SurgeryEventData

end PoincareConjecture
