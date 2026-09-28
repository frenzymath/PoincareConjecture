import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Limit.DerivativeBounds

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

open Set

theorem eventually_compact_curvatureDerivativeNorm_le_of_local_derivative_estimates
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Ioo T' T)
    (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ t ∈ I, ∀ x ∈ F.zeroBall A,
        (F.flow.connection t).curvatureDerivativeNorm m x ≤ D := by
  rcases eq_empty_or_nonempty I with rfl | hInonempty
  · refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro k
    dsimp
    intro t ht
    exact False.elim ht
  obtain ⟨tmin, htmin, hmin⟩ :=
    hIcompact.exists_isMinOn hInonempty continuousOn_id
  obtain ⟨tmax, htmax, hmax⟩ :=
    hIcompact.exists_isMaxOn hInonempty continuousOn_id
  let a : ℝ := (T' + tmin) / 2
  let b : ℝ := (T + tmax) / 2
  have ha : T' < a := by
    dsimp [a]
    linarith [(hI htmin).1, H.time_bounds.1]
  have hb : b < T := by
    dsimp [b]
    linarith [(hI htmax).2, H.time_bounds.2]
  have hIcc : I ⊆ Icc a b := by
    intro t ht
    have hleft : tmin ≤ t := by simpa using hmin ht
    have hright : t ≤ tmax := by simpa using hmax ht
    dsimp [a, b]
    constructor <;> linarith [(hI ht).1, (hI ht).2, (hI htmin).1, (hI htmax).2]
  obtain ⟨D, hD, hbound⟩ :=
    H.eventually_two_time_curvatureDerivativeNorm_le_of_local_derivative_estimates
      hShi a b ha hb A hA m
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with k hk
  dsimp only at hk ⊢
  intro t ht x hx
  exact hk 0 ⟨H.time_bounds.1, H.time_bounds.2⟩ t
    (hIcc ht) x hx

theorem eventually_compact_curvatureDerivativeNorm_le
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0})
    {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Ioo T' T)
    (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ t ∈ I, ∀ x ∈ F.zeroBall A,
        (F.flow.connection t).curvatureDerivativeNorm m x ≤ D :=
  H.eventually_compact_curvatureDerivativeNorm_le_of_local_derivative_estimates
    hM04.local_derivative_estimates hIcompact hI A hA m

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
