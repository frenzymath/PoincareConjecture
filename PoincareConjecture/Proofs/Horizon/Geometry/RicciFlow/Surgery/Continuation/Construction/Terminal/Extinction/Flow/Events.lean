import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Family
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Nonempty
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.Transport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.Splice

variable (F : SurgeryFlowData.{u}) (T : ℝ) (C : GeneralizedSliceCarrier.{u})
  {B : ℝ≥0∞} (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})

def oldEvent (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] :
    SurgeryEventData F.standard_initial F.local_constants F.parameters
      (slice F T C R) (metric F T C R) U :=
  (F.event U hU).copyPast (future := family F T C R)
    (fun _t ht => (family_before F T C R (ht.2.trans_lt hUT)).symm)

@[simp] theorem oldEvent_tMinus (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] :
    (oldEvent F T C R U hU hUT).tMinus = (F.event U hU).tMinus := rfl

theorem oldEvent_pre_identify (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] (t : Ico (F.event U hU).tMinus U)
    (x : (F.slice (F.event U hU).tMinus).carrier) :
    (oldEvent F T C R U hU hUT).pre_identify t
      (identifyBefore F T C R _ ((F.event U hU).tMinus_lt.trans hUT) x) =
        identifyBefore F T C R t.1 (t.2.2.trans hUT) ((F.event U hU).pre_identify t x) :=
  (F.event U hU).copyPast_pre_identify_apply
    (past := fun q => ⟨F.slice q, F.metric q⟩) (future := family F T C R)
    (fun _q hq => (family_before F T C R (hq.2.trans_lt hUT)).symm) t x

theorem oldEvent_pre_inverse (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] (t : Ico (F.event U hU).tMinus U)
    (x : (F.slice (F.event U hU).tMinus).carrier) :
    ((oldEvent F T C R U hU hUT).pre_identify t).symm
      (identifyBefore F T C R t.1 (t.2.2.trans hUT) ((F.event U hU).pre_identify t x)) =
        identifyBefore F T C R _ ((F.event U hU).tMinus_lt.trans hUT) x := by
  apply ((oldEvent F T C R U hU hUT).pre_identify t).injective
  exact (((oldEvent F T C R U hU hUT).pre_identify t).apply_symm_apply _).trans
    (oldEvent_pre_identify F T C R U hU hUT t x).symm

theorem oldEvent_retained_pre_image (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] :
    identifyBefore F T C R _ ((F.event U hU).tMinus_lt.trans hUT) ''
      (F.event U hU).retained_pre = (oldEvent F T C R U hU hUT).retained_pre :=
  (F.event U hU).copyPast_retained_pre_image
    (past := fun q => ⟨F.slice q, F.metric q⟩) (future := family F T C R)
    (fun _q hq => (family_before F T C R (hq.2.trans_lt hUT)).symm)

theorem oldEvent_retained_post_image (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] :
    identifyBefore F T C R U hUT '' (F.event U hU).retained_post =
      (oldEvent F T C R U hU hUT).retained_post :=
  (F.event U hU).copyPast_retained_post_image
    (past := fun q => ⟨F.slice q, F.metric q⟩) (future := family F T C R)
    (fun _q hq => (family_before F T C R (hq.2.trans_lt hUT)).symm)

theorem oldEvent_retention_map (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] (x : (F.slice (F.event U hU).tMinus).carrier) :
    (oldEvent F T C R U hU hUT).retention.map
      (identifyBefore F T C R _ ((F.event U hU).tMinus_lt.trans hUT) x) =
        identifyBefore F T C R U hUT ((F.event U hU).retention.map x) :=
  (F.event U hU).copyPast_retention_map
    (past := fun q => ⟨F.slice q, F.metric q⟩) (future := family F T C R)
    (fun _q hq => (family_before F T C R (hq.2.trans_lt hUT)).symm) x

theorem oldEvent_preservation (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] :
    M33NonemptyEventDataPreservation (F.event U hU) (oldEvent F T C R U hU hUT) :=
  (F.event U hU).copyPast_preservation
    (past := fun q => ⟨F.slice q, F.metric q⟩) (future := family F T C R)
    (fun _q hq => (family_before F T C R (hq.2.trans_lt hUT)).symm)

theorem oldEvent_limit_inverse (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T)
    [Nonempty (F.slice U).carrier] (x : (F.event U hU).terminal.carrier) :
    (oldEvent F T C R U hU hUT).limit_identify.inverse x =
      identifyBefore F T C R _ ((F.event U hU).tMinus_lt.trans hUT)
        ((F.event U hU).limit_identify.inverse x) := by
  have hcopy {p q : SurgeryEventRebuild.SliceMetric.{u}} (h : p = q)
      (S : GeneralizedSliceCarrier.{u}) (A : Set p.1.carrier) (B : Set S.carrier)
      (e : SurgeryRegionEquivalence p.1 S A B) (y : S.carrier) :
      (SurgeryEventRebuild.regionSource h S A B e).inverse y =
        SurgeryEventRebuild.identify p q h (e.inverse y) := by
    subst q
    rfl
  exact hcopy
    (Splice.family_before F T C R ((F.event U hU).tMinus_lt.trans hUT)).symm
    (F.event U hU).terminal (F.event U hU).regular_limit univ
    (F.event U hU).limit_identify x

def vanishingEvent (V : SurgeryVanishingEventData F.parameters F.slice F.metric T) :
    SurgeryVanishingEventData F.parameters (slice F T C R) (metric F T C R) T :=
  V.copyBefore (future := family F T C R)
    (fun _t ht => (family_before F T C R ht.2).symm)

@[simp] theorem vanishingEvent_tMinus
    (V : SurgeryVanishingEventData F.parameters F.slice F.metric T) :
    (vanishingEvent F T C R V).tMinus = V.tMinus := rfl

theorem vanishingEvent_pre_identify
    (V : SurgeryVanishingEventData F.parameters F.slice F.metric T)
    (t : Ico V.tMinus T) (x : (F.slice V.tMinus).carrier) :
    (vanishingEvent F T C R V).pre_identify t
      (identifyBefore F T C R _ V.tMinus_lt x) =
        identifyBefore F T C R t.1 t.2.2 (V.pre_identify t x) :=
  V.copyBefore_pre_identify_apply
    (past := fun q => ⟨F.slice q, F.metric q⟩) (future := family F T C R)
    (fun _q hq => (family_before F T C R hq.2).symm) t x

theorem oldEvent_slab_compatibility (hF : F.time_domain = Ico 0 T)
    (U : ℝ) (hU : U ∈ F.surgery_times) (hUT : U < T) [Nonempty (F.slice U).carrier]
    (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hfree : Disjoint (eventTimes F T) (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico (F.event U hU).tMinus U)
    (ht' : t ∈ Ico (F.event U hU).tMinus U)
    (x : (slice F T C R (F.event U hU).tMinus).carrier) :
    (regularSlab F T C R hF hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
        ((oldEvent F T C R U hU hUT).pre_identify ⟨s, hs'⟩ x) =
      (oldEvent F T C R U hU hUT).pre_identify ⟨t, ht'⟩ x := by
  have hb : b < T := (slab_side F T hfree).resolve_right
    (fun ha => (not_lt_of_ge (ha.trans hs.1)) (hs'.2.trans hUT))
  have hold : Icc a b ⊆ F.time_domain := by
    intro r hr
    rw [hF]
    exact ⟨(hJ hr).1, hr.2.trans_lt hb⟩
  have hfreeold := hfree.mono_left (subset_insert T F.surgery_times)
  obtain ⟨y, rfl⟩ := (identifyBefore F T C R _ ((F.event U hU).tMinus_lt.trans hUT)).surjective x
  exact (congrArg ((regularSlab F T C R hF hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩)
    (oldEvent_pre_identify F T C R U hU hUT ⟨s, hs'⟩ y)).trans
      ((regularSlab_transport_before F T C R hF hab hJ hfree hb hold hfreeold
        ⟨s, hs⟩ ⟨t, ht⟩ ((F.event U hU).pre_identify ⟨s, hs'⟩ y)).trans
        ((congrArg (identifyBefore F T C R t (ht'.2.trans hUT))
          (F.event_slab_compatibility U hU a b hab hold hfreeold s t hs ht hs' ht' y)).trans
            (oldEvent_pre_identify F T C R U hU hUT ⟨t, ht'⟩ y).symm))

theorem vanishingEvent_slab_compatibility (hF : F.time_domain = Ico 0 T)
    (V : SurgeryVanishingEventData F.parameters F.slice F.metric T)
    (hV : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
      ∀ hs' : s ∈ Ico V.tMinus T, ∀ ht' : t ∈ Ico V.tMinus T, ∀ x,
        (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
          (V.pre_identify ⟨s, hs'⟩ x) = V.pre_identify ⟨t, ht'⟩ x)
    (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hfree : Disjoint (eventTimes F T) (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico V.tMinus T) (ht' : t ∈ Ico V.tMinus T)
    (x : (slice F T C R V.tMinus).carrier) :
    (regularSlab F T C R hF hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
        ((vanishingEvent F T C R V).pre_identify ⟨s, hs'⟩ x) =
      (vanishingEvent F T C R V).pre_identify ⟨t, ht'⟩ x := by
  have hb : b < T := (slab_side F T hfree).resolve_right
    (fun ha => (not_lt_of_ge (ha.trans hs.1)) hs'.2)
  have hold : Icc a b ⊆ F.time_domain := by
    intro r hr
    rw [hF]
    exact ⟨(hJ hr).1, hr.2.trans_lt hb⟩
  have hfreeold := hfree.mono_left (subset_insert T F.surgery_times)
  obtain ⟨y, rfl⟩ := (identifyBefore F T C R _ V.tMinus_lt).surjective x
  exact (congrArg ((regularSlab F T C R hF hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩)
    (vanishingEvent_pre_identify F T C R V ⟨s, hs'⟩ y)).trans
      ((regularSlab_transport_before F T C R hF hab hJ hfree hb hold hfreeold
        ⟨s, hs⟩ ⟨t, ht⟩ (V.pre_identify ⟨s, hs'⟩ y)).trans
        ((congrArg (identifyBefore F T C R t ht'.2)
          (hV a b hab hold hfreeold s t hs ht hs' ht' y)).trans
            (vanishingEvent_pre_identify F T C R V ⟨t, ht'⟩ y).symm))

end PoincareConjecture.Surgery.Splice
