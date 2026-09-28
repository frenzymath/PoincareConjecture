import PoincareConjecture.Proofs.M63.Mathlib.PeriodicQuadraticBarrier
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.RatioRegularity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63SmoothCurvatureSquared_shortTime (F : RicciFlow n M (Icc a b))
    (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c) {K0 K1 K2 R : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hE : M62CurveEstimates F c K0 K1 K2) (hR : 0 < R)
    (hshort : (2 + m62C0 K0 K1 K2) * R * (b - a) ≤ 1 / 2)
    (hinit : ∀ x, m62CurvatureSquared F c a x + 1 ≤ R) :
    ∀ x t, t ∈ Icc a b →
      m62CurvatureSquared F c t x + 1 ≤
        R / (1 - (2 + m62C0 K0 K1 K2) * R * (t - a)) ∧
      R / (1 - (2 + m62C0 K0 K1 K2) * R * (t - a)) ≤ 2 * R := by
  have hab : a < b := by
    obtain ⟨s, hs, r, hr, hne⟩ := F.nontrivial
    by_contra! h
    exact hne (by linarith [hs.1, hs.2, hr.1, hr.2])
  have hC : 0 ≤ m62C0 K0 K1 K2 := by unfold m62C0; positivity
  apply Poincare.Parabolic.periodic_le_quadratic_barrier
    (U := fun x t => m62CurvatureSquared F c t x + 1)
    (V := fun x t => m62SpatialEvolutionRhs F c t x)
    (p := curvePeriod) (by unfold curvePeriod; positivity) hab
    (by positivity) hR hshort
    ((M62.curvatureSquared_continuousOn F c hc).add continuousOn_const)
    (fun t ht x => by simp only [m63CurvatureSquared_periodic F c hc ht x])
    (fun x t ht => (M62.hasDerivAt_curvatureSquared F c hc ht x).add_const 1)
    _ hinit
  intro x t ht hmax
  have hmaxq : IsLocalMax (m62CurvatureSquared F c t) x := by
    filter_upwards [hmax] with y hy
    change m62CurvatureSquared F c t y + 1 ≤ m62CurvatureSquared F c t x + 1 at hy
    change m62CurvatureSquared F c t y ≤ m62CurvatureSquared F c t x
    linarith
  have hq : ContDiff ℝ ∞ (m62CurvatureSquared F c t) :=
    (M62.curvatureSquared_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (M62.speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hvi := hv.inv (fun y => (M62.speed_pos F c hc (Ioo_subset_Icc_self ht) y).ne')
  have hdiff : m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x ≤ 0 :=
    Poincare.Parabolic.weighted_deriv_nonpos_of_isLocalMax hmaxq hq.continuous.continuousAt
      (hvi.differentiable (by simp) x)
      ((contDiff_infty_iff_deriv.mp hq).2.differentiable (by simp) x)
  have hnormal : 0 ≤ (F.metric t).inner (c x t) (m62SpatialNormalDerivative F c t x)
      (m62SpatialNormalDerivative F c t x) :=
    ((F.metric t).toRiemannianMetric.toCore (c x t)).re_inner_nonneg _
  have hqn := M62.curvatureSquared_nonneg F c t x
  have hksq := M62.curvature_sq F c t x
  have hk : m62Curvature F c t x ≤ m62CurvatureSquared F c t x + 1 := by
    nlinarith [sq_nonneg (m62Curvature F c t x - 1)]
  have hsum : m62CurvatureSquared F c t x + m62Curvature F c t x ≤
      (m62CurvatureSquared F c t x + 1) ^ 2 := by
    nlinarith [sq_nonneg (m62CurvatureSquared F c t x)]
  have hsquare : (m62CurvatureSquared F c t x) ^ 2 ≤
      (m62CurvatureSquared F c t x + 1) ^ 2 := by nlinarith
  have hbound := hE.spatial_squared_bound t ht x
  rw [(M62.hasDerivAt_curvatureSquared F c hc ht x).deriv] at hbound
  nlinarith only [hbound, hdiff, hnormal, hsquare, mul_le_mul_of_nonneg_left hsum hC]

end PoincareConjecture
