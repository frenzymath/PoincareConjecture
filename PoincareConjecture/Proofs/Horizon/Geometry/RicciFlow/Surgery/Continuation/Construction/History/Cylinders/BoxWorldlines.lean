import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.RegularHistory.Cylinders

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (e : SurgeryFlowCylinder F C origin scale J U)

theorem ordinary_box_tracks (A : OrdinaryTimeWindow W)
    (s : ℝ) (hs : s ∈ J) (hsA : origin + s / scale ∈ A.interval)
    (t : ℝ) (ht : t ∈ J) (htA : origin + t / scale ∈ A.interval)
    (x : C.carrier) (hx : x ∈ U) (y : A.box.carrier.carrier)
    (hy : forward W (origin + s / scale) (A.box.forward _ hsA y) = e.forward s hs x) :
    forward W (origin + t / scale) (A.box.forward _ htA y) = e.forward t ht x := by
  rw [← A.slab_compatibility A.lower A.upper A.ordered
    (A.slab_subset.trans W.time_subset) (A.surgery_free.mono_right Ioc_subset_Icc_self)
    (origin + s / scale) (origin + t / scale) (A.interval_subset hsA)
    (A.interval_subset htA) hsA htA y, hy]
  exact e.slab_compatibility A.lower A.upper A.ordered
    (A.slab_subset.trans W.time_subset) (A.surgery_free.mono_right Ioc_subset_Icc_self)
    s hs t ht (A.interval_subset hsA) (A.interval_subset htA) x hx

theorem event_box_tracks (s : ℝ) (hs : s ∈ J)
    (hT : origin + s / scale ∈ F.surgery_times)
    (hTW : origin + s / scale ∈ W.interval)
    [Nonempty (F.slice (origin + s / scale)).carrier]
    (A : EventTimeWindow W hT hTW)
    (t : ℝ) (ht : t ∈ J) (htA : origin + t / scale ∈ A.interval)
    (x : C.carrier) (hx : x ∈ U) (y : (EventIdentify.carrier hT).carrier)
    (hy : forward W (origin + s / scale) (A.identify _ A.time_mem y) = e.forward s hs x) :
    forward W (origin + t / scale) (A.identify _ htA y) = e.forward t ht x := by
  let E := F.event (origin + s / scale) hT
  by_cases hpre : origin + t / scale < origin + s / scale
  · have htPre := A.pre_subset ⟨htA, hpre⟩
    have hxPre := e.pre_retained_at_surgery s hs hT t ht htPre x hx
    have hret := e.surgery_compatibility s hs hT t ht htPre x hx
    rw [A.forward_identify_event] at hy
    have hcoord : (E.pre_identify ⟨origin + t / scale, htPre⟩).symm
        (e.forward t ht x) = y.val := by
      have heq := congrArg E.retention.inverse (hret.trans hy.symm)
      exact (E.retention.left_inverse (interior_subset hxPre)).symm.trans
        (heq.trans (E.retention.left_inverse (interior_subset y.property)))
    rw [A.identify_of_pre _ htA hpre]
    change E.pre_identify ⟨origin + t / scale, htPre⟩ y.val = e.forward t ht x
    rw [← hcoord]
    exact (E.pre_identify ⟨origin + t / scale, htPre⟩).apply_symm_apply _
  · by_cases hr : A.right ∈ W.interval
    · have hsPost : origin + s / scale ∈ Icc (origin + s / scale) A.right :=
        ⟨le_rfl, A.right_gt.le⟩
      have htPost : origin + t / scale ∈ Icc (origin + s / scale) A.right :=
        ⟨le_of_not_gt hpre, htA.2.2.le⟩
      rw [← A.identify_slab_compatibility (origin + s / scale) A.right A.right_gt
        ((A.post_subset hr).trans W.time_subset) (A.post_surgery_free hr)
        (origin + s / scale) (origin + t / scale) hsPost htPost A.time_mem htA y, hy]
      exact e.slab_compatibility (origin + s / scale) A.right A.right_gt
        ((A.post_subset hr).trans W.time_subset) (A.post_surgery_free hr)
        s hs t ht hsPost htPost x hx
    · have hclock : origin + t / scale = origin + s / scale := le_antisymm
        ((A.right_status.resolve_left hr) _ htA.1) (le_of_not_gt hpre)
      have hts : t = s := (div_left_inj' e.scale_pos.ne').mp (add_left_cancel hclock)
      subst t
      exact hy



theorem exists_tracking_box
    (L : ∀ t, t ∈ F.surgery_times → t ∈ W.interval →
      RicciFlowLocalTheory 3 (F.slice t).carrier)
    (htime : ∀ s ∈ J, origin + s / scale ∈ W.interval) (s : ℝ) (hs : s ∈ J) :
    ∃ b : BoxIndex W, ∃ hb : origin + s / scale ∈ (atlasBox W L b).interval,
      Function.Surjective ((atlasBox W L b).forward _ hb) ∧
      ∀ t ht (htb : origin + t / scale ∈ (atlasBox W L b).interval) x, x ∈ U →
        ∀ y, forward W (origin + s / scale) ((atlasBox W L b).forward _ hb y) =
          e.forward s hs x →
        forward W (origin + t / scale) ((atlasBox W L b).forward _ htb y) =
          e.forward t ht x := by
  classical
  by_cases hT : origin + s / scale ∈ F.surgery_times
  · let q : {t // t ∈ F.surgery_times ∩ W.interval} :=
      ⟨origin + s / scale, hT, htime s hs⟩
    let := W.slice_nonempty _ (htime s hs)
    refine ⟨Sum.inr ⟨q⟩, (eventWindow W q).time_mem,
      (eventWindow W q).box_event_surjective _, ?_⟩
    intro t ht htb x hx y hy
    exact event_box_tracks e s hs hT (htime s hs) (eventWindow W q) t ht htb x hx y hy
  · let z : (slice W (origin + s / scale)).carrier :=
      Classical.choice ((slice_nonempty_iff W _).mpr (htime s hs))
    obtain ⟨A, hA, hsA, _⟩ :=
      (Classical.choose_spec (exists_countable_ordinary_boxes W)).2 _ (htime s hs) hT z
    refine ⟨Sum.inl ⟨⟨A, hA⟩⟩, hsA, A.box_forward_surjective _ hsA, ?_⟩
    intro t ht htb x hx y hy
    exact ordinary_box_tracks e A s hs hsA t ht htb x hx y hy

end PoincareConjecture.Surgery.RegularHistory.Cylinders
