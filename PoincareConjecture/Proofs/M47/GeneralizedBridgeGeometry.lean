import PoincareConjecture.Proofs.M33.RegularHistory
import PoincareConjecture.Proofs.M33.HistoryMetric
import PoincareConjecture.Definitions.M28BoundedDistance
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W)

theorem regular_history_interval_nonnegative : H.generalized.interval ⊆ Ici 0 :=
  H.history.time_subset.trans F.time_domain_nonnegative

noncomputable def regular_history_slice_chart (t : ℝ) (ht : t ∈ H.generalized.interval) :
    PartialDiffeomorph (𝓡 3) (𝓡 3)
      (H.generalized.slice t).carrier (F.slice t).carrier ∞ where
  toFun := H.history.forward t ht
  invFun := H.history.inverse t ht
  source := univ
  target := range (H.history.forward t ht)
  map_source' x _ := mem_range_self x
  map_target' _ _ := mem_univ _
  left_inv' x _ := H.history.left_inverse t ht x
  right_inv' _ hx := H.history.right_inverse t ht hx
  open_source := isOpen_univ
  open_target := (H.history.forward_openEmbedding t ht).isOpen_range
  contMDiffOn_toFun := (H.history.forward_smooth t ht).contMDiffOn
  contMDiffOn_invFun := H.history.inverse_smooth t ht

noncomputable def regular_history_slice_diffeomorph (t : ℝ)
    (ht : t ∈ H.generalized.interval) (hregular : t ∉ F.surgery_times) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (H.generalized.slice t).carrier (F.slice t).carrier ∞ where
  toFun := H.history.forward t ht
  invFun := H.history.inverse t ht
  left_inv := H.history.left_inverse t ht
  right_inv x := H.history.right_inverse t ht (by
    rw [H.regular_range, m33RegularRegion_of_regular F t hregular]
    exact mem_univ x)
  contMDiff_toFun := H.history.forward_smooth t ht
  contMDiff_invFun := by
    have hi := H.history.inverse_smooth t ht
    rw [H.regular_range, m33RegularRegion_of_regular F t hregular] at hi
    exact contMDiffOn_univ.mp hi

theorem regular_history_hamiltonIvey
    (hpinched : ∀ t ∈ W.interval, SurgeryPinchedAt (F.connection t) t) :
    generalizedHamiltonIveyPinched H.generalized := by
  intro t ht
  obtain ⟨hnonnegative, hscalar, hnegative⟩ := hpinched t (H.interval_eq ▸ ht)
  refine ⟨ht, hnonnegative, ?_, ?_⟩
  · intro x
    simpa only [GeneralizedRicciFlowData.scalar, H.scalar_pullback t ht] using
      hscalar (H.history.forward t ht x) (mem_univ _)
  · intro x hx
    have h := hnegative (H.history.forward t ht x) (mem_univ _) (by
      simpa only [H.negative_part_pullback t ht] using hx)
    simpa only [GeneralizedRicciFlowData.scalar, H.scalar_pullback t ht,
      H.negative_part_pullback t ht] using h

theorem regular_history_ball_image (t : ℝ) (ht : t ∈ H.generalized.interval)
    (hregular : t ∉ F.surgery_times) (x : (H.generalized.slice t).carrier) (r : ℝ) :
    H.history.forward t ht '' (H.generalized.metric t).ball x r =
      (F.metric t).ball (H.history.forward t ht x) r := by
  apply H.history.ball_image_of_subset t ht x r
  rw [H.regular_range, m33RegularRegion_of_regular F t hregular]
  exact subset_univ _

theorem regular_history_ball_volume (t : ℝ) (ht : t ∈ H.generalized.interval)
    (hregular : t ∉ F.surgery_times) (x : (H.generalized.slice t).carrier) (r : ℝ) :
    calibratedMetricVolume (H.generalized.metric t) ((H.generalized.metric t).ball x r) =
      calibratedMetricVolume (F.metric t) ((F.metric t).ball (H.history.forward t ht x) r) := by
  rw [← H.volume_image t ht, regular_history_ball_image H t ht hregular x r]

end PoincareConjecture.M47
