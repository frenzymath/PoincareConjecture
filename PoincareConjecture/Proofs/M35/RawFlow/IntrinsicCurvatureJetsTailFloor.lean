import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSlabContinuity
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSlopeBounds











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness



theorem raw_intrinsic_warping_tail_floor
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T : ℝ} (hT : 0 ≤ T) (hTlt : T < G.lifetime) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 1,
      c ≤ rawWarpingRadius P G hrotation t r := by
  have ht (t : ℝ) (h : t ∈ Icc 0 T) : t ∈ Ico 0 G.lifetime :=
    ⟨h.1, h.2.trans_lt hTlt⟩
  have hc : ContinuousOn (fun t => rawWarpingRadius P G hrotation t 1) (Icc 0 T) :=
    (rawWarpingRadius_continuousOn_slab G P hrotation hT hTlt).comp
      (continuousOn_id.prodMk continuousOn_const) (fun _ ha => ⟨ha, mem_univ _⟩)
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT) hc
  have hpos : 0 < rawWarpingRadius P G hrotation a 1 := by
    rw [rawWarpingRadius_eq P G hrotation (ht a ha)]
    exact intrinsicWarpingRadius_pos _ _ _ zero_lt_one
  refine ⟨rawWarpingRadius P G hrotation a 1, hpos, ?_⟩
  intro t htime r hr
  have hs : ContDiff ℝ ∞ (rawWarpingRadius P G hrotation t) := by
    rw [rawWarpingRadius_eq P G hrotation (ht t htime)]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hmono : MonotoneOn (rawWarpingRadius P G hrotation t) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hs.continuous.continuousOn
      (hs.differentiable (by simp)).differentiableOn
    intro s hs
    exact (rawWarpingSlope_bounds P G hrotation (ht t htime) (interior_subset hs)).1
  have hone : (1 : ℝ) ∈ Ici 0 := by norm_num
  have hrad : r ∈ Ici 0 := by change (0 : ℝ) ≤ r; exact zero_le_one.trans hr
  exact (hmin htime).trans (hmono hone hrad hr)

end PoincareConjecture.M35.Uniqueness
