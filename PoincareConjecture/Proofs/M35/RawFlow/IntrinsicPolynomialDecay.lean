import PoincareConjecture.Proofs.M35.RawFlow.InitialSlopeSupport
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSlabContinuity
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSlopeBounds
import PoincareConjecture.Proofs.M35.RadialGauge.PolynomialComparison

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

include H

theorem raw_initial_slope_support :
    ∃ R : ℝ, 0 < R ∧ ∀ s, R ≤ s → rawWarpingSlope P G hrotation 0 s = 0 := by
  obtain ⟨R, hR, hslope⟩ := initial_intrinsic_slope_support g₀ H
  refine ⟨R, hR, ?_⟩
  intro s hs
  have ht : (0 : ℝ) ∈ Ico 0 G.lifetime := ⟨le_rfl, G.lifetime_pos⟩
  change deriv (rawWarpingRadius P G hrotation 0) s = 0
  rw [rawWarpingRadius_eq P G hrotation ht]
  have htransport (g h : RiemannianMetric 3 StandardCapSpace)
      (hg : _) (hc : MetricComplete g) (hh : _) (hd : MetricComplete h)
      (heq : g = h) : intrinsicWarpingRadius g hg hc =
        intrinsicWarpingRadius h hh hd := by
    subst h
    rfl
  rw [htransport _ _ _ _ _ _ G.initial_metric]
  exact hslope s hs

theorem raw_intrinsic_slope_polynomial_decay {T : ℝ} (hT : 0 < T)
    (hTlt : T < G.lifetime) :
    ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ s ≥ 0,
      (1 + s ^ 2) ^ N * rawWarpingSlope P G hrotation t s ≤ C := by
  obtain ⟨R, _, hstart⟩ := raw_initial_slope_support P H G hrotation
  obtain ⟨K, hK, hcurv⟩ := G.curvature_locally_bounded T hT.le hTlt
  obtain ⟨V, hV, hvelocity⟩ := raw_intrinsic_radial_velocity_bounded P G hT.le hTlt
  have hvalid (t : ℝ) (ht : t ∈ Icc 0 T) : t ∈ Ico 0 G.lifetime :=
    ⟨ht.1, ht.2.trans_lt hTlt⟩
  have hcont := (rawWarpingSlope_continuousOn_slab G P hrotation hT.le hTlt).mono
    (show Icc 0 T ×ˢ Ici (0 : ℝ) ⊆ Icc 0 T ×ˢ univ from
      fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hv (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (_hs : 0 ≤ s) :
      |rawRadialVelocity P G hrotation t s| ≤ V := by
    rw [rawRadialVelocity_eq P G hrotation (hvalid t ht)]
    exact hvelocity t ht (hrotation t (hvalid t ht)) s
  have hc (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : 0 ≤ s) :
      rawTangentialCurvature P G hrotation t s ≤ 9 * K :=
    (rawTangentialCurvature_bounds P G hrotation hK hTlt
      (fun t ht x => (le_abs_self _).trans (hcurv t ht x)) ht hs).2
  refine RadialGauge.halfLine_polynomial_bound_of_initial_support
    hT (mul_nonneg (by norm_num) hK) hV.le hcont
    (fun t ht => rawWarpingSlope_contDiff P G hrotation (hvalid t ht))
    (fun t ht s hs => (rawWarpingSlope_bounds P G hrotation (hvalid t ht) hs).2)
    hv hc hstart ?_
  intro t ht s hs
  exact (rawWarpingSlope_hasDerivAt_time P G hrotation
    ⟨ht.1, ht.2.trans_lt hTlt⟩ hs).hasDerivWithinAt

end PoincareConjecture.M35.Uniqueness
