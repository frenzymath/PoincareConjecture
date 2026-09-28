import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas.TimeWindows

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)
  {T : ℝ} (hT : T ∈ F.surgery_times) (hTW : T ∈ W.interval)

structure EventTimeWindow where
  left : ℝ
  right : ℝ
  pre_start_lt : (@SurgeryFlowData.event F T hT (W.slice_nonempty T hTW)).tMinus < left
  left_lt : left < T
  right_gt : T < right
  events_unique : ∀ s ∈ W.interval, left ≤ s → s ≤ right → s ∈ F.surgery_times → s = T
  right_status : right ∈ W.interval ∨ ∀ s ∈ W.interval, s ≤ T

variable {W hT hTW}

namespace EventTimeWindow

variable (A : EventTimeWindow W hT hTW)

def interval : Set ℝ := W.interval ∩ Ioo A.left A.right

theorem time_mem : T ∈ A.interval := ⟨hTW, A.left_lt, A.right_gt⟩

theorem time_subset : A.interval ⊆ W.interval := inter_subset_left

theorem interval_connected : A.interval.OrdConnected := W.interval_connected.inter ordConnected_Ioo

theorem interval_nontrivial : A.interval.Nontrivial :=
  nontrivial_inter_Ioo W.interval_connected W.interval_nontrivial hTW A.left_lt A.right_gt

theorem relatively_open : ∃ U : Set ℝ, IsOpen U ∧ A.interval = W.interval ∩ U :=
  ⟨Ioo A.left A.right, isOpen_Ioo, rfl⟩

theorem left_mem : A.left ∈ W.interval := by
  have hzero : 0 ≤ A.left :=
    (@SurgeryFlowData.event F T hT (W.slice_nonempty T hTW)).tMinus_nonnegative.trans
      A.pre_start_lt.le
  exact W.interval_connected.out W.zero_mem hTW ⟨hzero, A.left_lt.le⟩

theorem pre_subset : A.interval ∩ Iio T ⊆
    Ico (@SurgeryFlowData.event F T hT (W.slice_nonempty T hTW)).tMinus T := by
  intro s hs
  exact ⟨(A.pre_start_lt.trans hs.1.2.1).le, hs.2⟩

theorem events_eq : F.surgery_times ∩ A.interval = {T} := by
  ext s
  constructor
  · rintro ⟨hs, hsA⟩
    exact A.events_unique s hsA.1 hsA.2.1.le hsA.2.2.le hs
  · intro hs
    have hsT : s = T := hs
    subst s
    exact ⟨hT, A.time_mem⟩

theorem regular_of_ne {s : ℝ} (hs : s ∈ A.interval) (hne : s ≠ T) :
    s ∉ F.surgery_times :=
  fun hS => hne (A.events_unique s hs.1 hs.2.1.le hs.2.2.le hS)

theorem post_subset (hr : A.right ∈ W.interval) : Icc T A.right ⊆ W.interval :=
  W.interval_connected.out hTW hr

theorem post_surgery_free (hr : A.right ∈ W.interval) :
    Disjoint F.surgery_times (Ioc T A.right) := by
  apply disjoint_left.mpr
  intro s hs hsI
  have hsW := A.post_subset hr ⟨hsI.1.le, hsI.2⟩
  exact hsI.1.ne' (A.events_unique s hsW (A.left_lt.trans hsI.1).le hsI.2 hs)

def postSlab (hr : A.right ∈ W.interval) :
    SurgeryRegularSlab F.slice F.metric T A.right :=
  F.regular_slabs T A.right A.right_gt ((A.post_subset hr).trans W.time_subset)
    (A.post_surgery_free hr)

theorem interval_eq_Ioc_of_terminal (hterminal : ∀ s ∈ W.interval, s ≤ T) :
    A.interval = Ioc A.left T := by
  ext s
  constructor
  · intro hs
    exact ⟨hs.2.1, hterminal s hs.1⟩
  · intro hs
    exact ⟨W.interval_connected.out A.left_mem hTW ⟨hs.1.le, hs.2⟩,
      hs.1, hs.2.trans_lt A.right_gt⟩

theorem interval_eq_Ioo_of_right_mem (hr : A.right ∈ W.interval) :
    A.interval = Ioo A.left A.right := by
  apply inter_eq_right.mpr
  intro s hs
  exact W.interval_connected.out A.left_mem hr ⟨hs.1.le, hs.2.le⟩

end EventTimeWindow

variable (W hT hTW)

theorem exists_eventTimeWindow : Nonempty (EventTimeWindow W hT hTW) := by
  have hfinite : ((F.surgery_times ∩ W.interval) \ {T}).Finite := W.events_finite.sdiff
  have hnot : T ∈ ((F.surgery_times ∩ W.interval) \ {T})ᶜ := by simp
  obtain ⟨l, r, hTr, hisolate⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hfinite.isClosed.isOpen_compl.mem_nhds hnot)
  let E := @SurgeryFlowData.event F T hT (W.slice_nonempty T hTW)
  let a := (max l E.tMinus + T) / 2
  have ha : max l E.tMinus < a ∧ a < T := by
    dsimp [a]
    have hmax : max l E.tMinus < T := max_lt hTr.1 E.tMinus_lt
    constructor <;> linarith
  have hla : l < a := (le_max_left _ _).trans_lt ha.1
  have hpre : E.tMinus < a := (le_max_right _ _).trans_lt ha.1
  have hunique : ∀ s ∈ W.interval, l < s → s < r → s ∈ F.surgery_times → s = T := by
    intro s hs hls hsr hS
    by_contra hne
    exact hisolate ⟨hls, hsr⟩ ⟨⟨hS, hs⟩, hne⟩
  by_cases hlater : ∃ b ∈ W.interval, T < b
  · obtain ⟨b, hb, hTb⟩ := hlater
    let d := (T + min r b) / 2
    have hd : T < d ∧ d < min r b := by
      dsimp [d]
      have hmin := lt_min hTr.2 hTb
      constructor <;> linarith
    refine ⟨⟨a, d, hpre, ha.2, hd.1, ?_, Or.inl ?_⟩⟩
    · intro s hs has hsd hS
      exact hunique s hs (hla.trans_le has) (hsd.trans_lt (hd.2.trans_le (min_le_left _ _))) hS
    · exact W.interval_connected.out hTW hb ⟨hd.1.le, hd.2.le.trans (min_le_right _ _)⟩
  · have hterminal : ∀ s ∈ W.interval, s ≤ T := by
      intro s hs
      exact le_of_not_gt (fun hTs => hlater ⟨s, hs, hTs⟩)
    refine ⟨⟨a, r, hpre, ha.2, hTr.2, ?_, Or.inr hterminal⟩⟩
    intro s hs has _ hS
    exact hunique s hs (hla.trans_le has) ((hterminal s hs).trans_lt hTr.2) hS

include hT hTW in

theorem event_postSlab_or_terminal :
    (∃ b : ℝ, T < b ∧ Icc T b ⊆ W.interval ∧
      Disjoint F.surgery_times (Ioc T b) ∧
      Nonempty (SurgeryRegularSlab F.slice F.metric T b)) ∨
      (∀ s ∈ W.interval, s ≤ T) := by
  obtain ⟨A⟩ := exists_eventTimeWindow W hT hTW
  rcases A.right_status with hr | hterminal
  · exact Or.inl ⟨A.right, A.right_gt, A.post_subset hr, A.post_surgery_free hr, ⟨A.postSlab hr⟩⟩
  · exact Or.inr hterminal

end PoincareConjecture.Surgery.RegularHistory
