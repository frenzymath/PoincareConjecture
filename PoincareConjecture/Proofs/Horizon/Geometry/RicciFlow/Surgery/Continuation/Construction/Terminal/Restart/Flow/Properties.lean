import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Conclusion


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.TerminalRestart

theorem pinchedAt_iff_hamiltonIvey {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (t : ℝ) :
    SurgeryPinchedAt D t ↔ HamiltonIveyPinchedAt D t := by
  simp only [SurgeryPinchedAt, SurgeryPinchedOn, HamiltonIveyPinchedAt, mem_univ, forall_true_left]

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (C : GeneralizedSliceCarrier.{u}) {B : ℝ≥0∞}
  (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})
  (E : SurgeryEventData F.standard_initial F.local_constants F.parameters
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

theorem time_domain_eq : (flow I C R E hC hRP hB hblow hE).time_domain =
    {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B} := rfl

theorem surgery_at_terminal : T ∈ (flow I C R E hC hRP hB hblow hE).surgery_times :=
  mem_insert _ _

theorem no_later_surgery (t : ℝ) (ht : T < t) :
    t ∉ (flow I C R E hC hRP hB hblow hE).surgery_times := no_later_event I t ht

theorem flow_nonempty (t : ℝ) (ht : t ∈ (flow I C R E hC hRP hB hblow hE).time_domain) :
    Nonempty ((flow I C R E hC hRP hB hblow hE).slice t).carrier :=
  slices_nonempty I C R t ht.1

theorem terminal_event_eq [Nonempty ((flow I C R E hC hRP hB hblow hE).slice T).carrier] :
    (flow I C R E hC hRP hB hblow hE).event T
      (surgery_at_terminal I C R E hC hRP hB hblow hE) = E :=
  event_terminal I C R E (mem_insert T F.surgery_times)

theorem post_terminal_interval : ∃ d : ℝ, 0 < d ∧
    Ioo T (T + d) ⊆ (flow I C R E hC hRP hB hblow hE).time_domain ∧
    Disjoint (flow I C R E hC hRP hB hblow hE).surgery_times (Ioo T (T + d)) := by
  have hinterval : ∃ d : ℝ, 0 < d ∧
      Ioo T (T + d) ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B} := by
    by_cases hfinite : B = ⊤
    · refine ⟨1, by norm_num, fun t ht => ⟨(I.terminal_pos.trans ht.1).le, ?_⟩⟩
      rw [hfinite]
      exact ENNReal.ofReal_lt_top
    · have hTB := (ENNReal.ofReal_lt_iff_lt_toReal I.terminal_pos.le hfinite).mp hB
      refine ⟨B.toReal - T, sub_pos.mpr hTB, fun t ht => ?_⟩
      have ht0 : 0 ≤ t := (I.terminal_pos.trans ht.1).le
      refine ⟨ht0, (ENNReal.ofReal_lt_iff_lt_toReal ht0 hfinite).mpr ?_⟩
      linarith [ht.2]
  obtain ⟨d, hd, hJ⟩ := hinterval
  exact ⟨d, hd, hJ, disjoint_left.mpr (fun t ht hti => no_later_event I t hti.1 ht)⟩

theorem pinched
    (hpinch : ∀ t, T ≤ t ∧ ENNReal.ofReal t < B → SurgeryPinchedAt (R.connection t) t) :
    SurgeryFlowPinched (flow I C R E hC hRP hB hblow hE) := by
  intro t ht
  have hcopy (p q : SurgeryEventRebuild.SliceMetric.{u}) (hpq : p = q)
      (D : LeviCivitaData p.2) (hD : SurgeryPinchedAt D t) :
      SurgeryPinchedAt
        (SurgeryEventRebuild.relabel (C := fun z => LeviCivitaData z.2) hpq D) t := by
    subst q
    exact hD
  change SurgeryPinchedAt (Splice.connection F T C R t) t
  unfold Splice.connection
  by_cases h : t < T
  · rw [dif_pos h]
    exact hcopy ⟨F.slice t, F.metric t⟩ _ (Splice.family_before F T C R h).symm
      (F.connection t) (I.pinched t (I.time_domain_eq ▸ (show t ∈ Ico 0 T from ⟨ht.1, h⟩)))
  · rw [dif_neg h]
    exact hcopy ⟨C, R.metric t⟩ _ (Splice.family_after F T C R (le_of_not_gt h)).symm
      (R.connection t) (hpinch t ⟨le_of_not_gt h, ht.2⟩)

theorem pinched_of_hamiltonIvey
    (hpinch : ∀ t, T ≤ t ∧ ENNReal.ofReal t < B → HamiltonIveyPinchedAt (R.connection t) t) :
    SurgeryFlowPinched (flow I C R E hC hRP hB hblow hE) :=
  pinched I C R E hC hRP hB hblow hE
    (fun t ht => (pinchedAt_iff_hamiltonIvey (R.connection t) t).mpr (hpinch t ht))

end PoincareConjecture.Surgery.TerminalRestart
