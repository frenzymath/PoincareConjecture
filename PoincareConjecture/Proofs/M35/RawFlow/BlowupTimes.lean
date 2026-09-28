import PoincareConjecture.Definitions.M34StandardCapExistence
import PoincareConjecture.Proofs.M10.ScalarBound
import Mathlib.Topology.Algebra.Order.Field










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PartialStandardCapFlow



theorem exists_unit_backward_duration_threshold {g₀ : StandardInitialMetric}
    (F : PartialStandardCapFlow g₀) :
    ∃ H : ℝ, 0 < H ∧ ∀ t ∈ Ico 0 F.lifetime, ∀ x : StandardCapSpace,
      H ≤ (F.flow.connection t).scalarCurvature x →
        1 ≤ t * (F.flow.connection t).scalarCurvature x := by
  have hhalf : 0 < F.lifetime / 2 := half_pos F.lifetime_pos
  have hhalfT : F.lifetime / 2 < F.lifetime := half_lt_self F.lifetime_pos
  obtain ⟨K, _, hK⟩ := F.curvature_locally_bounded (F.lifetime / 2) hhalf.le hhalfT
  refine ⟨max (9 * K) (2 / F.lifetime) + 1, ?_, ?_⟩
  · have hmax := le_max_right (9 * K) (2 / F.lifetime)
    have hpos : 0 < 2 / F.lifetime := div_pos (by norm_num) F.lifetime_pos
    linarith
  · intro t ht x hR
    have hlarge : 9 * K < (F.flow.connection t).scalarCurvature x := by
      linarith [le_max_left (9 * K) (2 / F.lifetime)]
    have hscale : 2 / F.lifetime ≤ (F.flow.connection t).scalarCurvature x := by
      linarith [le_max_right (9 * K) (2 / F.lifetime)]
    have htime : F.lifetime / 2 < t := by
      by_contra h
      have hn := (le_abs_self _).trans (hK t ⟨ht.1, le_of_not_gt h⟩ x)
      have hs := M10.abs_scalarCurvature_le (F.flow.metric t) (F.flow.connection t) x
      norm_num at hs
      linarith [le_abs_self ((F.flow.connection t).scalarCurvature x)]
    have hpos : 0 ≤ (F.flow.connection t).scalarCurvature x :=
      (div_nonneg (by norm_num) F.lifetime_pos.le).trans hscale
    have hprod := (div_le_iff₀ F.lifetime_pos).mp hscale
    nlinarith [mul_nonneg (sub_nonneg.mpr htime.le) hpos]


theorem tendsto_time_of_scalar_diverges {g₀ : StandardInitialMetric}
    (F : PartialStandardCapFlow g₀) (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 F.lifetime)
    (hR : Tendsto (fun k => (F.flow.connection (t k)).scalarCurvature (x k)) atTop atTop) :
    Tendsto t atTop (𝓝 F.lifetime) := by
  apply tendsto_order.2
  constructor
  · intro T hT
    by_cases hT0 : 0 ≤ T
    · obtain ⟨K, _, hK⟩ := F.curvature_locally_bounded T hT0 hT
      filter_upwards [hR.eventually_gt_atTop (9 * K)] with k hk
      by_contra hkt
      have hnorm := (le_abs_self _).trans (hK (t k) ⟨(ht k).1, le_of_not_gt hkt⟩ (x k))
      have hscalar := M10.abs_scalarCurvature_le (F.flow.metric (t k))
        (F.flow.connection (t k)) (x k)
      have hle := le_abs_self ((F.flow.connection (t k)).scalarCurvature (x k))
      norm_num at hscalar
      linarith
    · exact Eventually.of_forall (fun k => lt_of_lt_of_le (lt_of_not_ge hT0) (ht k).1)
  · intro T hT
    exact Eventually.of_forall (fun k => (ht k).2.trans hT)


theorem tendsto_scalar_mul_time_of_diverges {g₀ : StandardInitialMetric}
    (F : PartialStandardCapFlow g₀) (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 F.lifetime)
    (hR : Tendsto (fun k => (F.flow.connection (t k)).scalarCurvature (x k)) atTop atTop) :
    Tendsto (fun k => (F.flow.connection (t k)).scalarCurvature (x k) * t k)
      atTop atTop :=
  hR.atTop_mul_pos F.lifetime_pos (F.tendsto_time_of_scalar_diverges t x ht hR)

end PoincareConjecture.PartialStandardCapFlow
