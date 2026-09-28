import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.Properties

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.TerminalRestart

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (C : GeneralizedSliceCarrier.{u}) {B : ℝ≥0∞}
  (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})

def finiteOrdinaryFlow (hB : ENNReal.ofReal T < B) (hfinite : B ≠ ⊤) :
    RicciFlow 3 C.carrier (Ico T B.toReal) := by
  have hTB := (ENNReal.ofReal_lt_iff_lt_toReal I.terminal_pos.le hfinite).mp hB
  refine Poincare.Geometry.RicciFlow.Harnack.restrictFlow R
    (fun t ht => ⟨ht.1, ?_⟩) ordConnected_Ico ?_
  · exact (ENNReal.ofReal_lt_iff_lt_toReal (I.terminal_pos.le.trans ht.1) hfinite).mpr ht.2
  · exact ⟨T, ⟨le_rfl, hTB⟩, (T + B.toReal) / 2,
      ⟨by linarith, by linarith⟩, by linarith⟩

theorem relabeled_flow_curvature {p q : SurgeryEventRebuild.SliceMetric.{u}}
    (hpq : p = q) {J : Set ℝ} (A : RicciFlow 3 p.1.carrier J) (t : ℝ)
    (x : p.1.carrier) :
    ((SurgeryEventRebuild.flow hpq A).connection t).curvatureTensorNorm
      (SurgeryEventRebuild.identify p q hpq x) = (A.connection t).curvatureTensorNorm x := by
  subst q
  rfl

variable (E : SurgeryEventData F.standard_initial F.local_constants F.parameters
    (Splice.slice F T C R) (Splice.metric F T C R) T)
  [Nonempty C.carrier] (hC : IsCompact (univ : Set C.carrier))
  (hRP : SurgeryNoTwoSidedProjectivePlane C) (hB : ENNReal.ofReal T < B)
  (hblow : B ≠ ⊤ → ∀ L s : ℝ, s < B.toReal →
    ∃ t ∈ Ioo (max T s) B.toReal, ∃ x : C.carrier,
      L < (R.connection t).curvatureTensorNorm x)
  (hE : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
    ∀ hs' : s ∈ Ico E.tMinus T, ∀ ht' : t ∈ Ico E.tMinus T, ∀ x,
      (Splice.regularSlab F T C R I.time_domain_eq hab hJ hfree).transport
        ⟨s, hs⟩ ⟨t, ht⟩ (E.pre_identify ⟨s, hs'⟩ x) = E.pre_identify ⟨t, ht'⟩ x)

def finiteEndSlab (hfinite : B ≠ ⊤) :
    RepairedPreterminalSlab (flow I C R E hC hRP hB hblow hE) B.toReal where
  start := T
  start_mem := ⟨I.terminal_pos.le, hB⟩
  start_lt := (ENNReal.ofReal_lt_iff_lt_toReal I.terminal_pos.le hfinite).mp hB
  start_initial_or_surgery := Or.inr (mem_insert T F.surgery_times)
  time_subset := fun t ht => ⟨I.terminal_pos.le.trans ht.1,
    (ENNReal.ofReal_lt_iff_lt_toReal (I.terminal_pos.le.trans ht.1) hfinite).mpr ht.2⟩
  surgery_free := disjoint_left.mpr (fun t ht hti => no_later_event I t hti.1 ht)
  flow := SurgeryEventRebuild.flow (Splice.family_after F T C R (le_refl T)).symm
    (finiteOrdinaryFlow I C R hB hfinite)
  identify t := SurgeryEventRebuild.diffeomorph
    (Splice.family_after F T C R (le_refl T)).symm
    (Splice.family_after F T C R t.property.1).symm (Diffeomorph.refl (𝓡 3) C.carrier ∞)
  initial_identify := by
    intro x
    obtain ⟨y, rfl⟩ := (Splice.identifyAfter F T C R T le_rfl).surjective x
    exact SurgeryEventRebuild.diffeomorph_apply
      (Splice.family_after F T C R (le_refl T)).symm
      (Splice.family_after F T C R (le_refl T)).symm
      (Diffeomorph.refl (𝓡 3) C.carrier ∞) y
  metric_pullback := by
    intro t
    exact SurgeryEventRebuild.diffeomorph_flow_metric_pullback
      (Splice.family_after F T C R (le_refl T)).symm
      (Splice.family_after F T C R t.property.1).symm
      (finiteOrdinaryFlow I C R hB hfinite) t.1
      (Diffeomorph.refl (𝓡 3) C.carrier ∞)
      (by intro x v w; simp [finiteOrdinaryFlow, Poincare.Geometry.RicciFlow.Harnack.restrictFlow])
  transport_compatibility := by
    intro a b hab hJ hfree s t hs ht hs' ht' x
    have ha : T ≤ a := (Splice.slab_side F T hfree).resolve_left
      (fun hb => (not_lt_of_ge hs'.1) (hs.2.trans_lt hb))
    obtain ⟨y, rfl⟩ := (Splice.identifyAfter F T C R T le_rfl).surjective x
    exact (congrArg ((flow I C R E hC hRP hB hblow hE).regular_slabs a b hab hJ hfree
      |>.transport ⟨s, hs⟩ ⟨t, ht⟩)
      (SurgeryEventRebuild.diffeomorph_apply
        (Splice.family_after F T C R (le_refl T)).symm
        (Splice.family_after F T C R hs'.1).symm
        (Diffeomorph.refl (𝓡 3) C.carrier ∞) y)).trans
      ((Splice.regularSlab_transport_after F T C R I.time_domain_eq
        hab hJ hfree ha ⟨s, hs⟩ ⟨t, ht⟩ y).trans
        (SurgeryEventRebuild.diffeomorph_apply
          (Splice.family_after F T C R (le_refl T)).symm
          (Splice.family_after F T C R ht'.1).symm
          (Diffeomorph.refl (𝓡 3) C.carrier ∞) y).symm)
  curvature_unbounded := by
    intro L s hs
    obtain ⟨t, ht, x, hx⟩ := hblow hfinite L s hs
    refine ⟨t, ht, Splice.identifyAfter F T C R T le_rfl x, ?_⟩
    exact lt_of_lt_of_eq hx (relabeled_flow_curvature
      (Splice.family_after F T C R (le_refl T)).symm
      (finiteOrdinaryFlow I C R hB hfinite) t x).symm

theorem finite_end_slab (hfinite : B ≠ ⊤) :
    ∃ next : RepairedPreterminalSlab (flow I C R E hC hRP hB hblow hE) B.toReal,
      next.start = T := ⟨finiteEndSlab I C R E hC hRP hB hblow hE hfinite, rfl⟩

end PoincareConjecture.Surgery.TerminalRestart
