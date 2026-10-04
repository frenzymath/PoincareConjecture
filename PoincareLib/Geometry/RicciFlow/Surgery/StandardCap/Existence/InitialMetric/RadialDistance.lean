import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.RadialBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.RegularizedNorm
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.GradientDistance

/-!
# Distance estimates for the initial cap

Morgan-Tian Lemma 12.2, printed pp. 294-295. A regularized radius has
differential bounded by the cap tangent norm, even at the tip. The path
distance estimates use the actual metric-selected tangent norms.
See `proof-work/tasks/M34/derivations/radial-distance.md`.
-/

set_option autoImplicit false

open Poincare Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareMT.M34

/-- The smooth regularized radius has speed at most the metric speed,
including at the origin (Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_regularizedRadius_speed {a e : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (he : 0 < e) (x v : StandardCapSpace) :
    |(regularizedNorm e x)⁻¹ * inner ℝ x v| ≤
      (capRiemannianMetric a ha hapi).tangentNorm x v := by
  have hg : 0 ≤ capMetricInner a x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (capMetricInner_pos ha.le hapi x v hv).le
  have hp := regularizedNorm_pos he x
  have hs : regularizedNorm e x ^ 2 = ‖x‖ ^ 2 + e ^ 2 :=
    Real.sq_sqrt (by positivity)
  have ht : Real.sqrt (capMetricInner a x v v) ^ 2 = capMetricInner a x v v :=
    Real.sq_sqrt hg
  have hr := capMetricInner_radial_lower ha.le hapi x v
  have hsq : (inner ℝ x v) ^ 2 ≤
      (regularizedNorm e x * Real.sqrt (capMetricInner a x v v)) ^ 2 := by
    rw [mul_pow, hs, ht]
    nlinarith [mul_nonneg (sq_nonneg e) hg]
  have habs : |inner ℝ x v| ≤
      regularizedNorm e x * Real.sqrt (capMetricInner a x v v) := by
    have hn := mul_nonneg hp.le (Real.sqrt_nonneg (capMetricInner a x v v))
    nlinarith [sq_abs (inner ℝ x v), abs_nonneg (inner ℝ x v)]
  change |(regularizedNorm e x)⁻¹ * inner ℝ x v| ≤ Real.sqrt (capMetricInner a x v v)
  rw [abs_mul, abs_inv, abs_of_pos hp, inv_mul_eq_div]
  exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using habs)

set_option backward.isDefEq.respectTransparency false in
/-- The regularized radius is nonexpanding for the actual cap distance
(Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_regularizedRadius_edist {a e : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (he : 0 < e) (x y : StandardCapSpace) :
    edist (regularizedNorm e x) (regularizedNorm e y) ≤
      (capRiemannianMetric a ha hapi).edist x y := by
  let g := capRiemannianMetric a ha hapi
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type) :=
    ⟨g.toRiemannianMetric⟩
  apply edist_le_riemannianEDist_of_mfderiv_le_one
    (contMDiff_iff_contDiff.mpr ((regularizedNorm_contDiff he).of_le (by simp)))
  intro z
  let L : TangentSpace (𝓡 3) z →L[ℝ] ℝ :=
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (regularizedNorm e) z
  change ‖L‖ₑ ≤ 1
  rw [← ofReal_norm, ENNReal.ofReal_le_one]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  change |L v| ≤
    Real.sqrt (capMetricInner a z v v)
  have hL : L = (regularizedNorm e z)⁻¹ • innerSL ℝ z := by
    simpa only [L, mfderiv_eq_fderiv] using (regularizedNorm_hasFDerivAt he z).fderiv
  rw [hL]
  exact capRiemannianMetric_regularizedRadius_speed ha hapi he z v

set_option backward.isDefEq.respectTransparency false in
/-- Ambient Euclidean distance is an upper bound for the actual cap
distance, by integrating the straight segment (Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_edist_le {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (x y : StandardCapSpace) :
    (capRiemannianMetric a ha hapi).edist x y ≤ edist x y := by
  let g := capRiemannianMetric a ha hapi
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type) :=
    ⟨g.toRiemannianMetric⟩
  change riemannianEDist (𝓡 3) x y ≤ edist x y
  calc
    _ ≤ (1 : ℝ≥0∞) * edist x y := by
      apply riemannianEDist_le_mul_edist_of_convex (I := 𝓡 3)
        (f := fun z : StandardCapSpace => z) (s := Set.univ) (K := 1)
        convex_univ (fun _ _ => contMDiffAt_id) ?_ (Set.mem_univ x) (Set.mem_univ y)
      intro z _
      let L : StandardCapSpace →L[ℝ] TangentSpace (𝓡 3) z :=
        mfderiv (𝓡 3) (𝓡 3) (fun z : StandardCapSpace => z) z
      change ‖L‖ₑ ≤ (1 : ℝ≥0)
      rw [← ofReal_norm, ENNReal.ofReal_le_coe]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      rw [one_mul]
      change g.tangentNorm z
        (mfderiv (𝓡 3) (𝓡 3) (fun z : StandardCapSpace => z) z v) ≤ ‖v‖
      rw [mfderiv_eq_fderiv, fderiv_fun_id]
      exact capRiemannianMetric_tangentNorm_le ha hapi z v
    _ = _ := one_mul _

/-- Distance from the tip is bounded below by the radial coordinate.
The positive regularization tends to zero only after the uniform distance
bound is established (Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_radius_le_edist {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (x : StandardCapSpace) :
    ENNReal.ofReal ‖x‖ ≤ (capRiemannianMetric a ha hapi).edist 0 x := by
  have hfinite : (capRiemannianMetric a ha hapi).edist 0 x ≠ ⊤ :=
    ne_top_of_le_ne_top (edist_ne_top 0 x) (capRiemannianMetric_edist_le ha hapi 0 x)
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr
  by_contra h
  have hlt : ((capRiemannianMetric a ha hapi).edist 0 x).toReal < ‖x‖ :=
    lt_of_not_ge h
  let e := (‖x‖ - ((capRiemannianMetric a ha hapi).edist 0 x).toReal) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have hb := capRiemannianMetric_regularizedRadius_edist ha hapi he 0 x
  rw [regularizedNorm_zero he.le, edist_dist, Real.dist_eq,
    ENNReal.ofReal_le_iff_le_toReal hfinite, abs_sub_comm] at hb
  have hs := (le_abs_self (regularizedNorm e x - e)).trans hb
  have hn := norm_le_regularizedNorm e x
  dsimp [e] at hs
  linarith

/-- Meridian arclength is the actual Riemannian distance from the tip,
including at the origin (Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_edist_zero {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (x : StandardCapSpace) :
    (capRiemannianMetric a ha hapi).edist 0 x = ENNReal.ofReal ‖x‖ := by
  apply le_antisymm
  · simpa only [edist_dist, dist_zero_left] using capRiemannianMetric_edist_le ha hapi 0 x
  · exact capRiemannianMetric_radius_le_edist ha hapi x

/-- Radial metric balls are exactly the ambient Euclidean balls,
also for nonpositive radii (Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_ball_zero {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (r : ℝ) :
    (capRiemannianMetric a ha hapi).ball 0 r = Metric.ball 0 r := by
  ext x
  simp only [RiemannianMetric.ball, Set.mem_ofPred_eq, capRiemannianMetric_edist_zero ha hapi,
    Metric.mem_ball, dist_zero_right]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)

/-- The closed radial core is a compact Euclidean ball. The nonnegative
radius hypothesis is essential for extended-real conversion
(Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_closedBall_zero {a r : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (hr : 0 ≤ r) :
    {x : StandardCapSpace | (capRiemannianMetric a ha hapi).edist 0 x ≤
      ENNReal.ofReal r} = Metric.closedBall 0 r := by
  ext x
  simp only [Set.mem_ofPred_eq, capRiemannianMetric_edist_zero ha hapi,
    Metric.mem_closedBall, dist_zero_right]
  exact ENNReal.ofReal_le_ofReal_iff hr

end PoincareMT.M34
