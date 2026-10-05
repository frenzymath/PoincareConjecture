import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularAnalytics
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.ScalarEvolution
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.TimeEstimate

/-!
# Scalar-time control on the actual selected generalized history

Box worldlines agree with the actual ordinary slab transports. After
identifying their scalar functions, the strict auxiliary threshold permits
extension across the finite old-event set by continuity of the derivative.
Sources: Morgan--Tian Assumptions 11.18, p. 279, Lemma 14.11 /
Proposition 14.12, pp. 349-350, and Section 17.2, pp. 409-410.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

namespace M48Predecessors

variable (P : M48Predecessors.{u}) {F : SurgeryFlowData.{u}} {T : ℝ}
  {L : RepairedPreterminalSlab F T} (R : M48RegularSpacetimeData L)

include P

/-- The scalar functions agree along the literal regular-slab worldline. -/
theorem regular_box_slab_scalar (b : R.history.generalized.box_index)
    (a c : ℝ) (hac : a < c) (hJ : Icc a c ⊆ F.time_domain)
    (hS : Disjoint F.surgery_times (Ioc a c))
    (t s : ℝ) (ht : t ∈ Icc a c) (hs : s ∈ Icc a c)
    (htb : t ∈ (R.history.generalized.box b).interval)
    (hsb : s ∈ (R.history.generalized.box b).interval)
    (x : (R.history.generalized.box b).carrier.carrier) :
    ((R.history.generalized.box b).flow.connection s).scalarCurvature x =
      ((F.regular_slabs a c hac hJ hS).flow.connection s).scalarCurvature
        (((F.regular_slabs a c hac hJ hS).identify ⟨t, ht⟩).symm
          (R.history.history.forward t (m33BoxIntervalSubset _ b htb)
            ((R.history.generalized.box b).forward t htb x))) := by
  let B := F.regular_slabs a c hac hJ hS
  rw [P.regular_box_scalar R b s hsb x]
  rw [← R.history.history.slab_compatibility b a c hac hJ hS t s ht hs htb hsb x]
  exact B.m48_scalarCurvature_eq ⟨s, hs⟩ (F.connection s) _

theorem regular_box_ordinary_derivative {J : Set ℝ} {r C : ℝ}
    (hJ : R.history.generalized.interval ⊆ J)
    (hderiv : SurgeryScalarDerivativeControlOn F J r C)
    (b : R.history.generalized.box_index) (t : ℝ)
    (ht : t ∈ interior (R.history.generalized.box b).interval)
    (hregular : t ∉ F.surgery_times)
    (x : (R.history.generalized.box b).carrier.carrier)
    (hQ : r⁻¹ ^ 2 ≤ ((R.history.generalized.box b).flow.connection t).scalarCurvature x) :
    ∃ d, HasDerivAt
      (fun s => ((R.history.generalized.box b).flow.connection s).scalarCurvature x) d t ∧
        |d| ≤ C * ((R.history.generalized.box b).flow.connection t).scalarCurvature x ^ 2 := by
  let E := F.surgery_times ∩ L.regularHistoryWindow.interval
  have hE : E.Finite := L.regularHistoryWindow.events_finite
  have hnot : t ∉ E := fun h => hregular h.1
  have hnb : ((R.history.generalized.box b).interval \ E) ∈ 𝓝 t :=
    inter_mem (mem_interior_iff_mem_nhds.mp ht) (hE.isClosed.isOpen_compl.mem_nhds hnot)
  obtain ⟨a, c, htc, hnbhd, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hnb
  have hti : t ∈ Ioo a c := Icc_mem_nhds_iff.mp hnbhd
  have hac : a < c := hti.1.trans hti.2
  have hbox : Icc a c ⊆ (R.history.generalized.box b).interval := fun s hs => (hsub hs).1
  have hdom : Icc a c ⊆ F.time_domain :=
    fun s hs => R.history.history.time_subset (m33BoxIntervalSubset _ b (hbox hs))
  have hfree : Disjoint F.surgery_times (Ioc a c) := by
    apply disjoint_left.mpr
    intro s hs hsc
    have hb := hsub ⟨hsc.1.le, hsc.2⟩
    apply hb.2
    exact ⟨hs, R.history.interval_eq ▸ m33BoxIntervalSubset _ b hb.1⟩
  let B := F.regular_slabs a c hac hdom hfree
  let y := (B.identify ⟨t, htc⟩).symm
    (R.history.history.forward t (m33BoxIntervalSubset _ b (interior_subset ht))
      ((R.history.generalized.box b).forward t (interior_subset ht) x))
  have heq (s : ℝ) (hs : s ∈ Icc a c) :
      ((R.history.generalized.box b).flow.connection s).scalarCurvature x =
        (B.flow.connection s).scalarCurvature y :=
    P.regular_box_slab_scalar R b a c hac hdom hfree t s htc hs
      (interior_subset ht) (hbox hs) x
  have hthreshold : r⁻¹ ^ 2 ≤ (B.flow.connection t).scalarCurvature y := by
    rw [← heq t htc]
    exact hQ
  obtain ⟨d, hd, hb⟩ := hderiv a c hac hdom hfree y t
    ⟨hJ (m33BoxIntervalSubset _ b (interior_subset ht)), hti⟩ hthreshold
  refine ⟨d, hd.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hnbhd] with s hs
    exact heq s hs
  · simpa only [heq t htc] using hb

/-- M31's full box-time estimate, including the retained points at old events. -/
theorem regular_box_derivative {J : Set ℝ} {r C r' : ℝ}
    (hJ : R.history.generalized.interval ⊆ J)
    (hderiv : SurgeryScalarDerivativeControlOn F J r C)
    (hmargin : r⁻¹ ^ 2 < r'⁻¹ ^ 2)
    (b : R.history.generalized.box_index) (t : ℝ)
    (ht : t ∈ (R.history.generalized.box b).interval)
    (x : (R.history.generalized.box b).carrier.carrier)
    (hQ : r'⁻¹ ^ 2 ≤ ((R.history.generalized.box b).flow.connection t).scalarCurvature x) :
    ∃ d, HasDerivWithinAt
      (fun s => ((R.history.generalized.box b).flow.connection s).scalarCurvature x) d
      (R.history.generalized.box b).interval t ∧
        |d| ≤ C * ((R.history.generalized.box b).flow.connection t).scalarCurvature x ^ 2 := by
  let E := F.surgery_times ∩ L.regularHistoryWindow.interval
  apply M48.time_estimate_extend (E := E)
    (R.history.generalized.box b).flow.interval.convex
    (R.history.generalized.box b).flow.nontrivial L.regularHistoryWindow.events_finite
    ((R.history.generalized.box b).flow.contDiffOn_scalarCurvature_timeSlice x)
    ?_ t ht (hmargin.trans_le hQ)
  intro s hs hqs
  apply P.regular_box_ordinary_derivative R hJ hderiv b s hs.1 _ x hqs.le
  intro hevent
  apply hs.2
  exact ⟨hevent, R.history.interval_eq ▸ m33BoxIntervalSubset _ b (interior_subset hs.1)⟩

end M48Predecessors

/-- Apply the actual calibrated estimate, with no supplied derivative premise. -/
theorem M48AnalyticCalibration.regular_time_derivative
    {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)
    (P : M48Predecessors.{u}) {p : SurgeryParameterPrefix S.constants}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (hp : S.SeedCompatible p) (old : SurgeryPrefixControls p F O)
    {Q : SurgeryNoncollapseExtension.{u} p} {N : SurgeryCanonicalExtension p Q}
    (controls : SurgeryEpochContinuationControls p F O Q N)
    {L : RepairedPreterminalSlab F O.H} (R : M48RegularSpacetimeData L)
    (b : R.history.generalized.box_index) (t : ℝ)
    (ht : t ∈ (R.history.generalized.box b).interval)
    (x : (R.history.generalized.box b).carrier.carrier)
    (hQ : (A.historyRadius N.rNext)⁻¹ ^ 2 ≤
      ((R.history.generalized.box b).flow.connection t).scalarCurvature x) :
    ∃ d, HasDerivWithinAt
      (fun s => ((R.history.generalized.box b).flow.connection s).scalarCurvature x) d
      (R.history.generalized.box b).interval t ∧
        |d| ≤ S.calibration.analytic_constant *
          ((R.history.generalized.box b).flow.connection t).scalarCurvature x ^ 2 := by
  apply P.regular_box_derivative R _ (A.continuation hp old controls).scalar_derivative
    (A.history_threshold N.r_pos) b t ht x hQ
  intro s hs
  exact (show s ∈ L.regularHistoryWindow.interval from R.history.interval_eq ▸ hs)

end PoincareMT
