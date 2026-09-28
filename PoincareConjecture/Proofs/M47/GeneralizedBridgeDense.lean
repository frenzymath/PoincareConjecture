import PoincareConjecture.Proofs.M47.GeneralizedBridgeCanonical
import PoincareConjecture.Definitions.M45ControlledSchedules
import PoincareConjecture.Proofs.M28.Sec10_1_Pinching
import Mathlib.Order.Interval.Set.Infinite











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W)



theorem exists_regular_history_slice_between {s a : ℝ}
    (hs : s ∈ H.generalized.interval) (hspos : 0 < s) (has : a < s) :
    ∃ u ∈ H.generalized.interval, a < u ∧ u < s ∧ u ∉ F.surgery_times := by
  have hmax : max 0 a < s := max_lt hspos has
  obtain ⟨u, hu, hnot⟩ := ((Ioo_infinite hmax).sdiff W.events_finite).nonempty
  have huW : u ∈ W.interval := W.interval_connected.out W.zero_mem (H.interval_eq ▸ hs)
    ⟨(le_max_left 0 a).trans hu.1.le, hu.2.le⟩
  refine ⟨u, H.interval_eq.symm ▸ huW, (le_max_right 0 a).trans_lt hu.1, hu.2, ?_⟩
  intro hEvent
  exact hnot ⟨hEvent, huW⟩



theorem regular_history_dense_canonical {epsilon C t : ℝ} (htpos : 0 < t)
    (x : (H.generalized.slice t).carrier)
    (hcanonical : ∀ s ∈ W.interval, s < t → s ∉ F.surgery_times →
      ∀ y : (F.slice s).carrier,
        4 * H.generalized.scalar ⟨t, x⟩ ≤ (F.connection s).scalarCurvature y →
          SurgeryCanonicalControl F s y epsilon C) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods H.generalized epsilon C t x := by
  intro s hs hst a has
  have hnonnegative := regular_history_interval_nonnegative H hs
  have chooseSlice : ∃ u ∈ H.generalized.interval,
      a < u ∧ u ≤ s ∧ u < t ∧ u ∉ F.surgery_times := by
    by_cases hz : s = 0
    · subst s
      exact ⟨0, hs, has, le_rfl, htpos, F.zero_not_surgery⟩
    · have hspos : 0 < s := lt_of_le_of_ne hnonnegative (Ne.symm hz)
      obtain ⟨u, hu, hau, hus, hregular⟩ := exists_regular_history_slice_between H hs hspos has
      exact ⟨u, hu, hau, hus.le, hus.trans_le hst, hregular⟩
  obtain ⟨u, hu, hau, hus, hut, hregular⟩ := chooseSlice
  refine ⟨u, hu, hau, hus, ?_⟩
  intro y hy
  apply regular_history_canonical_control H hu hregular y
  apply hcanonical u (H.interval_eq ▸ hu) hut hregular
  simpa only [GeneralizedRicciFlowData.scalar, H.scalar_pullback u hu] using hy




theorem exists_regular_history_bounded_distance
    (S : RepairedControlledSchedulesData.{u}) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon₀ : epsilon ≤ S.calibration.epsilon₁₀)
    (C : ℝ) (hC : 0 < C) (A : ℝ) (hA : 0 ≤ A) :
    ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
      ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F)
        (H : M33RegularHistoryData W),
      (∀ s ∈ W.interval, SurgeryPinchedAt (F.connection s) s) →
      ∀ t, t ∈ H.generalized.interval → 0 < t →
      ∀ x : (H.generalized.slice t).carrier, D₀ ≤ H.generalized.scalar ⟨t, x⟩ →
      (∀ s ∈ W.interval, s < t → s ∉ F.surgery_times →
        ∀ y : (F.slice s).carrier,
          4 * H.generalized.scalar ⟨t, x⟩ ≤ (F.connection s).scalarCurvature y →
            SurgeryCanonicalControl F s y epsilon C) →
      RepairedBoundedDistanceEstimate H.generalized A D t x := by
  obtain ⟨D₀, D, hD₀, hD, hbound⟩ :=
    S.calibration.bounded_distance_dense epsilon hepsilon hepsilon₀ C hC A hA
  refine ⟨D₀, D, hD₀, hD, ?_⟩
  intro F W H hpinched t ht htpos x hx hcanonical
  exact hbound H.generalized
    (regular_history_hamiltonIvey H hpinched).weak t ht x hx
    (regular_history_dense_canonical H htpos x hcanonical)

end PoincareConjecture.M47
