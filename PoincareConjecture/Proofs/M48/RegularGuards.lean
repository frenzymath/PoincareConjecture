import PoincareConjecture.Proofs.M48.RegularSpacetime










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

namespace M33RegularHistoryData

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) (t : ℝ) (ht : t ∈ H.generalized.interval)
  (hregular : t ∉ F.surgery_times)

include hregular in
theorem regular_range_univ : range (H.history.forward t ht) = univ :=
  (H.regular_range t ht).trans (m33RegularRegion_of_regular F t hregular)


def regularDiffeomorph : Diffeomorph (𝓡 3) (𝓡 3)
    (H.generalized.slice t).carrier (F.slice t).carrier ∞ where
  toFun := H.history.forward t ht
  invFun := H.history.inverse t ht
  left_inv := H.history.left_inverse t ht
  right_inv x := H.history.right_inverse t ht (by
    rw [H.regular_range_univ t ht hregular]
    exact mem_univ x)
  contMDiff_toFun := H.history.forward_smooth t ht
  contMDiff_invFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (H.history.inverse t ht)
    apply contMDiffOn_univ.mp
    simpa only [H.regular_range_univ t ht hregular] using H.history.inverse_smooth t ht

include ht hregular in
theorem regular_slice_compact :
    IsCompact (univ : Set (H.generalized.slice t).carrier) := by
  apply (H.history.forward_openEmbedding t ht).isEmbedding.isCompact_iff.mpr
  rw [image_univ, H.regular_range_univ t ht hregular]
  exact F.slices_compact t (H.history.time_subset ht)

end M33RegularHistoryData

namespace RepairedPreterminalSlab

variable {F : SurgeryFlowData.{u}} {T : ℝ} (L : RepairedPreterminalSlab F T)

def singularCatalog (_L : RepairedPreterminalSlab F T) : Set ℝ :=
  insert T (F.surgery_times ∩ Ico 0 T)

theorem singularCatalog_finite : L.singularCatalog.Finite :=
  L.initial_events_finite.insert T

theorem terminal_mem_singularCatalog : T ∈ L.singularCatalog := mem_insert _ _

theorem mem_singularCatalog_iff {t : ℝ} (ht : t ∈ Ico 0 T) :
    t ∈ L.singularCatalog ↔ t ∈ F.surgery_times := by
  simp only [singularCatalog, mem_insert_iff, mem_inter_iff]
  constructor
  · rintro (h | h)
    · exact (ht.2.ne h).elim
    · exact h.1
  · exact fun h => Or.inr ⟨h, ht⟩

theorem zero_not_mem_singularCatalog : 0 ∉ L.singularCatalog := by
  have hT : 0 < T := (F.time_domain_nonnegative L.start_mem).trans_lt L.start_lt
  exact fun h => F.zero_not_surgery ((L.mem_singularCatalog_iff ⟨le_rfl, hT⟩).mp h)


theorem singularCatalog_discrete (s : ℝ) (_hs : s ∈ L.singularCatalog) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ L.singularCatalog, t ≠ s → δ ≤ |t - s| := by
  have hopen := (L.singularCatalog_finite.sdiff (t := {s})).isClosed.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen s (by simp)
  refine ⟨δ, hδ, ?_⟩
  intro t ht hne
  by_contra h
  have hmem : t ∈ Metric.ball s δ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using lt_of_not_ge h
  exact hball hmem ⟨ht, by simpa using hne⟩

end RepairedPreterminalSlab


theorem M48RegularSpacetimeData.regular_slices_compact
    {F : SurgeryFlowData.{u}} {T : ℝ} {L : RepairedPreterminalSlab F T}
    (R : M48RegularSpacetimeData L) (t : ℝ)
    (ht : t ∈ R.history.generalized.interval) (hregular : t ∉ L.singularCatalog) :
    IsCompact (univ : Set (R.history.generalized.slice t).carrier) := by
  apply R.history.regular_slice_compact t ht
  have ht' : t ∈ L.regularHistoryWindow.interval := R.history.interval_eq ▸ ht
  exact fun hevent => hregular ((L.mem_singularCatalog_iff
    (show t ∈ Ico 0 T from ht')).mpr hevent)

theorem SurgeryPrefixControls.two_epsilon_le_threshold
    {S : RepairedControlledSchedulesData.{u}} {p : SurgeryParameterPrefix S.constants}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hp : S.SeedCompatible p) :
    2 * F.parameters.epsilon ≤ 1 / 200 := by
  rw [old.epsilon_eq, hp.setup_eq]
  exact S.calibration.two_epsilon_le_bounded_distance.trans S.calibration.epsilon₁₀_le





theorem SurgeryPrefixControls.terminal_epsilon_le_threshold
    {S : RepairedControlledSchedulesData.{u}} {p : SurgeryParameterPrefix S.constants}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hp : S.SeedCompatible p) :
    terminalAccuracyFactor * F.parameters.epsilon ≤ 1 / 200 := by
  rw [old.epsilon_eq, hp.setup_eq]
  have hhalf : S.setup.epsilon ≤ S.calibration.common_epsilon := by
    linarith [S.calibration.two_epsilon_le_common, S.setup.epsilon_pos]
  exact (mul_le_mul_of_nonneg_left hhalf terminalAccuracyFactor_pos.le).trans
    (S.calibration.terminal_common_epsilon_le_appendixA.trans
      S.calibration.appendixA.epsilon₀_le_one_two_hundred)

end PoincareConjecture
