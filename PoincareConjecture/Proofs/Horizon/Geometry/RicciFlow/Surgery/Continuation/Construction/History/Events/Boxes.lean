import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Events.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas.Compatibility











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.RegularHistory

namespace EventIdentify

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F} {T : ℝ}
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] (hTW : T ∈ W.interval)

theorem carrier_nonempty : Nonempty (carrier hT).carrier := by
  obtain ⟨y, hy⟩ := (F.event T hT).retained_post_interior_nonempty
  exact ⟨(F.event T hT).retention.interiorDiffeomorph.symm ⟨y, hy⟩⟩


def atEvent : (carrier hT).carrier → (slice W T).carrier :=
  fun x => ⟨(F.event T hT).retention.map x.val, hTW, by
    rw [m33RegularRegion_of_surgery F T hT]
    exact (F.event T hT).retention.mapsTo_interior x.property⟩

@[simp] theorem forward_atEvent (x : (carrier hT).carrier) :
    forward W T (atEvent hT hTW x) = (F.event T hT).retention.map x.val := rfl

theorem atEvent_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ (atEvent hT hTW) :=
  (ContMDiff.subtypeVal_comp_iff (regionOpens W T) _).mp
    (F.event T hT).retention.interiorMap_isLocalDiffeomorph.contMDiff

theorem atEvent_openEmbedding : Topology.IsOpenEmbedding (atEvent hT hTW) := by
  apply Topology.IsOpenEmbedding.of_comp _ (forward_openEmbedding W T)
  exact isOpen_interior.isOpenEmbedding_subtypeVal.comp
    (F.event T hT).retention.interiorDiffeomorph.toHomeomorph.isOpenEmbedding

theorem atEvent_surjective : Function.Surjective (atEvent hT hTW) := by
  intro y
  have hy : y.val ∈ interior (F.event T hT).retained_post := by
    simpa only [m33RegularRegion_of_surgery F T hT] using y.property.2
  obtain ⟨x, hx, hxy⟩ := (F.event T hT).retention.image_interior.symm ▸ hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem atEvent_metric (x : (carrier hT).carrier) (v w : TangentSpace (𝓡 3) x) :
    (metric W T).inner (atEvent hT hTW x)
      (mfderiv (𝓡 3) (𝓡 3) (atEvent hT hTW) x v)
      (mfderiv (𝓡 3) (𝓡 3) (atEvent hT hTW) x w) =
      (F.metric T).inner ((F.event T hT).retention.interiorMap x)
        (mfderiv (𝓡 3) (𝓡 3) (F.event T hT).retention.interiorMap x v)
        (mfderiv (𝓡 3) (𝓡 3) (F.event T hT).retention.interiorMap x w) := by
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (forward W T) (atEvent hT hTW x)
        (mfderiv (𝓡 3) (𝓡 3) (atEvent hT hTW) x z) =
      mfderiv (𝓡 3) (𝓡 3) (F.event T hT).retention.interiorMap x z :=
    (mfderiv_comp_apply x ((forward_smooth W T).mdifferentiable (by simp) _)
      ((atEvent_smooth hT hTW).mdifferentiable (by simp) x) z).symm
  rw [← metric_pullback W T, hderiv v, hderiv w]
  rfl

end EventIdentify

namespace EventTimeWindow

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F} {T : ℝ}
    {hT : T ∈ F.surgery_times} {hTW : T ∈ W.interval}
    [Nonempty (F.slice T).carrier] (A : EventTimeWindow W hT hTW)


def identify (t : ℝ) (ht : t ∈ A.interval) :
    (EventIdentify.carrier hT).carrier → (slice W t).carrier := by
  by_cases hpre : t < T
  · exact EventIdentify.pre hT ⟨t, A.pre_subset ⟨ht, hpre⟩⟩ ht.1
      (A.regular_of_ne ht hpre.ne)
  · by_cases hr : A.right ∈ W.interval
    · exact EventIdentify.post hT (A.postSlab hr) ⟨t, le_of_not_gt hpre, ht.2.2.le⟩ ht.1
        (fun hs => A.events_unique t ht.1 ht.2.1.le ht.2.2.le hs)
    · have heq : t = T := le_antisymm
        ((A.right_status.resolve_left hr) t ht.1) (le_of_not_gt hpre)
      subst t
      exact EventIdentify.atEvent hT hTW

theorem identify_of_pre (t : ℝ) (ht : t ∈ A.interval) (hpre : t < T) :
    A.identify t ht = EventIdentify.pre hT ⟨t, A.pre_subset ⟨ht, hpre⟩⟩ ht.1
      (A.regular_of_ne ht hpre.ne) := by
  simp only [identify, dif_pos hpre]

theorem identify_of_post (hr : A.right ∈ W.interval) (t : ℝ)
    (ht : t ∈ A.interval) (hpost : T ≤ t) :
    A.identify t ht =
      EventIdentify.post hT (A.postSlab hr) ⟨t, hpost, ht.2.2.le⟩ ht.1
        (fun hs => A.events_unique t ht.1 ht.2.1.le ht.2.2.le hs) := by
  simp only [identify, dif_neg (not_lt.mpr hpost), dif_pos hr]

theorem identify_at_terminal (hr : A.right ∉ W.interval) :
    A.identify T A.time_mem = EventIdentify.atEvent hT hTW := by
  simp only [identify, dif_neg (lt_irrefl T), dif_neg hr]

theorem identify_smooth (t : ℝ) (ht : t ∈ A.interval) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (A.identify t ht) := by
  by_cases hpre : t < T
  · rw [A.identify_of_pre t ht hpre]
    exact EventIdentify.pre_smooth _ _ _ _
  · by_cases hr : A.right ∈ W.interval
    · rw [A.identify_of_post hr t ht (le_of_not_gt hpre)]
      exact EventIdentify.post_smooth _ _ _ _ _
    · have heq : t = T := le_antisymm
        ((A.right_status.resolve_left hr) t ht.1) (le_of_not_gt hpre)
      subst t
      rw [A.identify_at_terminal hr]
      exact EventIdentify.atEvent_smooth _ _

theorem identify_openEmbedding (t : ℝ) (ht : t ∈ A.interval) :
    Topology.IsOpenEmbedding (A.identify t ht) := by
  by_cases hpre : t < T
  · rw [A.identify_of_pre t ht hpre]
    exact EventIdentify.pre_openEmbedding _ _ _ _
  · by_cases hr : A.right ∈ W.interval
    · rw [A.identify_of_post hr t ht (le_of_not_gt hpre)]
      exact EventIdentify.post_openEmbedding _ _ _ _ _
    · have heq : t = T := le_antisymm
        ((A.right_status.resolve_left hr) t ht.1) (le_of_not_gt hpre)
      subst t
      rw [A.identify_at_terminal hr]
      exact EventIdentify.atEvent_openEmbedding _ _

theorem identify_event_surjective : Function.Surjective (A.identify T A.time_mem) := by
  by_cases hr : A.right ∈ W.interval
  · rw [A.identify_of_post hr T A.time_mem le_rfl]
    exact EventIdentify.post_event_surjective hT (A.postSlab hr) hTW
  · rw [A.identify_at_terminal hr]
    exact EventIdentify.atEvent_surjective hT hTW

@[simp] theorem forward_identify_event (x : (EventIdentify.carrier hT).carrier) :
    forward W T (A.identify T A.time_mem x) = (F.event T hT).retention.map x.val := by
  by_cases hr : A.right ∈ W.interval
  · rw [A.identify_of_post hr T A.time_mem le_rfl]
    exact (A.postSlab hr).initial_identify _
  · rw [A.identify_at_terminal hr]
    rfl


theorem exists_flow_metric (L : RicciFlowLocalTheory 3 (F.slice T).carrier) :
    ∃ H : RicciFlow 3 (EventIdentify.carrier hT).carrier A.interval,
      ∀ t (ht : t ∈ A.interval) x (v w : TangentSpace (𝓡 3) x),
        (metric W t).inner (A.identify t ht x)
          (mfderiv (𝓡 3) (𝓡 3) (A.identify t ht) x v)
          (mfderiv (𝓡 3) (𝓡 3) (A.identify t ht) x w) =
            (H.metric t).inner x v w := by
  by_cases hr : A.right ∈ W.interval
  · obtain ⟨H, hpre, hpost⟩ := A.exists_flow_of_right_mem hr
    refine ⟨H, ?_⟩
    intro t ht x v w
    by_cases hlt : t < T
    · rw [A.identify_of_pre t ht hlt, ← hpre ⟨ht, hlt⟩]
      exact EventIdentify.pre_metric hT ⟨t, A.pre_subset ⟨ht, hlt⟩⟩ ht.1
        (A.regular_of_ne ht hlt.ne) x v w
    · rw [A.identify_of_post hr t ht (le_of_not_gt hlt),
        ← hpost ⟨ht, le_of_not_gt hlt⟩]
      exact EventIdentify.post_metric hT (A.postSlab hr)
        ⟨t, le_of_not_gt hlt, ht.2.2.le⟩ ht.1
        (fun hs => A.events_unique t ht.1 ht.2.1.le ht.2.2.le hs) x v w
  · have hterminal := A.right_status.resolve_left hr
    obtain ⟨H, hpre, hTmetric⟩ := A.exists_flow_of_terminal L hterminal
    refine ⟨H, ?_⟩
    intro t ht x v w
    by_cases hlt : t < T
    · rw [A.identify_of_pre t ht hlt, ← hpre ⟨ht, hlt⟩]
      exact EventIdentify.pre_metric hT ⟨t, A.pre_subset ⟨ht, hlt⟩⟩ ht.1
        (A.regular_of_ne ht hlt.ne) x v w
    · have heq : t = T := le_antisymm (hterminal t ht.1) (le_of_not_gt hlt)
      subst t
      rw [A.identify_at_terminal hr, EventIdentify.atEvent_metric]
      exact (hTmetric x v w).symm

def flow (L : RicciFlowLocalTheory 3 (F.slice T).carrier) :
    RicciFlow 3 (EventIdentify.carrier hT).carrier A.interval :=
  Classical.choose (A.exists_flow_metric L)

theorem identify_metric (L : RicciFlowLocalTheory 3 (F.slice T).carrier)
    (t : ℝ) (ht : t ∈ A.interval) (x : (EventIdentify.carrier hT).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (metric W t).inner (A.identify t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (A.identify t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (A.identify t ht) x w) =
        ((A.flow L).metric t).inner x v w :=
  Classical.choose_spec (A.exists_flow_metric L) t ht x v w


def box (L : RicciFlowLocalTheory 3 (F.slice T).carrier) :
    GeneralizedRicciFlowBox (slice W) (metric W) W.interval := by
  letI := EventIdentify.carrier_nonempty hT
  exact {
    carrier := EventIdentify.carrier hT
    interval := A.interval
    relatively_open := A.relatively_open
    flow := A.flow L
    forward := A.identify
    inverse t ht := Function.invFun (A.identify t ht)
    forward_openEmbedding := A.identify_openEmbedding
    forward_smooth := A.identify_smooth
    inverse_smooth t ht := ((A.flow L).metric t).contMDiffOn_invFun_of_injective_pullback_eq
      (metric W t) (A.identify_smooth t ht) (A.identify_openEmbedding t ht).injective
      (A.identify_metric L t ht)
    left_inverse t ht := Function.leftInverse_invFun (A.identify_openEmbedding t ht).injective
    right_inverse t ht := by
      rintro _ ⟨x, rfl⟩
      rw [Function.leftInverse_invFun (A.identify_openEmbedding t ht).injective]
    metric_pullback := A.identify_metric L }

theorem box_event_surjective (L : RicciFlowLocalTheory 3 (F.slice T).carrier) :
    Function.Surjective ((A.box L).forward T A.time_mem) := A.identify_event_surjective

theorem identify_slab_compatibility (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (hfree : Disjoint F.surgery_times (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ A.interval) (ht' : t ∈ A.interval)
    (x : (EventIdentify.carrier hT).carrier) :
    (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      (forward W s (A.identify s hs' x)) = forward W t (A.identify t ht' x) := by
  have hsame : s < T ↔ t < T := by
    constructor
    · intro hsT
      by_contra htT
      exact Set.disjoint_left.mp hfree hT
        ⟨hs.1.trans_lt hsT, (le_of_not_gt htT).trans ht.2⟩
    · intro htT
      by_contra hsT
      exact Set.disjoint_left.mp hfree hT
        ⟨ht.1.trans_lt htT, (le_of_not_gt hsT).trans hs.2⟩
  by_cases hsT : s < T
  · have htT := hsame.mp hsT
    rw [A.identify_of_pre s hs' hsT, A.identify_of_pre t ht' htT]
    exact EventIdentify.pre_slab_compatibility hT a b hab hJ hfree
      ⟨s, A.pre_subset ⟨hs', hsT⟩⟩ ⟨t, A.pre_subset ⟨ht', htT⟩⟩ hs ht _ _ _ _ x
  · have htT : ¬ t < T := mt hsame.mpr hsT
    by_cases hr : A.right ∈ W.interval
    · rw [A.identify_of_post hr s hs' (le_of_not_gt hsT),
        A.identify_of_post hr t ht' (le_of_not_gt htT)]
      exact EventIdentify.post_slab_compatibility hT A.right_gt
        ((A.post_subset hr).trans W.time_subset) (A.post_surgery_free hr)
        a b hab hJ hfree ⟨s, le_of_not_gt hsT, hs'.2.2.le⟩
        ⟨t, le_of_not_gt htT, ht'.2.2.le⟩ hs ht _ _ _ _ x
    · have hterminal := A.right_status.resolve_left hr
      have hsEq : s = T := le_antisymm (hterminal s hs'.1) (le_of_not_gt hsT)
      have htEq : t = T := le_antisymm (hterminal t ht'.1) (le_of_not_gt htT)
      subst s
      subst t
      simp only [SurgeryRegularSlab.transport, Diffeomorph.apply_symm_apply]


theorem box_slab_compatibility (L : RicciFlowLocalTheory 3 (F.slice T).carrier) :
    SlabCompatible (A.box L) := A.identify_slab_compatibility

theorem box_events_unique (L : RicciFlowLocalTheory 3 (F.slice T).carrier)
    {t : ℝ} (ht : t ∈ (A.box L).interval) (htS : t ∈ F.surgery_times) : t = T :=
  A.events_unique t ht.1 ht.2.1.le ht.2.2.le htS

end EventTimeWindow

end PoincareConjecture.Surgery.RegularHistory
