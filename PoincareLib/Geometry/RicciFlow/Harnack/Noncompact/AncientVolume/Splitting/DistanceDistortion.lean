import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Calabi
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Continuity
import PoincareLib.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Additive distance distortion on controlled Ricci-flow regions

The actual Calabi upper supports, reversed in time, give upper right slopes
for distance. The one-sided comparison theorem integrates these slopes.
Joint distance continuity and the support functions are derived from the
flow, completeness, and Ricci bounds.

This is the bounded time-shift comparison needed when applying the spatial
selection in Kleiner--Lott (corrected 2013), Proposition 41.13, p. 2678,
to the buffered ancient compactness construction of Corollary 44.1,
pp. 2682--2683. It does not identify a line in the limit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Poincare.AncientVolume

private theorem image_le_add_of_upper_supports
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ t ∈ Ico a b, ∃ u : ℝ → ℝ,
      u t = f t ∧ (∀ s, f s ≤ u s) ∧ DifferentiableAt ℝ u t ∧ deriv u t ≤ C) :
    f b ≤ f a + C * (b - a) := by
  have hbar (t : ℝ) : HasDerivAt (fun s => f a + C * (s - a)) C t := by
    convert! (((hasDerivAt_id t).sub_const a).const_mul C).const_add (f a) using 1
    simp
  apply image_le_of_liminf_slope_right_le_deriv_boundary hf
    (by simp : f a ≤ f a + C * (a - a))
    (fun t _ => (hbar t).continuousAt.continuousWithinAt)
    (fun t _ => (hbar t).hasDerivWithinAt) ?_ ⟨hab, le_rfl⟩
  intro t ht r hr
  obtain ⟨u, heq, hupper, hu, hder⟩ := hsupport t ht
  have hu' : HasDerivWithinAt u (deriv u t) (Ici t) t := hu.hasDerivAt.hasDerivWithinAt
  have hfreq := hu'.liminf_right_slope_le (hder.trans_lt hr)
  apply (hfreq.and_eventually self_mem_nhdsWithin).mono
  intro s hs
  have hts : 0 < s - t := sub_pos.mpr hs.2
  have hsl : slope f t s ≤ slope u t s := by
    rw [slope_def_field, slope_def_field, heq]
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hupper s) _) hts.le
  exact hsl.trans_lt hs.1

/-- Smooth upper supports with a uniform derivative lower bound control
backward increments of a continuous real function. -/
theorem backward_image_le_add_of_upper_supports
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hsupport : ∀ t ∈ Ioc a b, ∃ u : ℝ → ℝ,
      u t = f t ∧ (∀ s, f s ≤ u s) ∧ DifferentiableAt ℝ u t ∧ -C ≤ deriv u t) :
    f a ≤ f b + C * (b - a) := by
  have hrev : ContinuousOn (fun t => f (-t)) (Icc (-b) (-a)) :=
    hf.comp continuous_neg.continuousOn (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have h := image_le_add_of_upper_supports (neg_le_neg hab) hrev (C := C) (by
    intro t ht
    obtain ⟨u, heq, hupper, hu, hder⟩ := hsupport (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hd : HasDerivAt (fun s => u (-s)) (-deriv u (-t)) t := by
      convert! hu.hasDerivAt.comp t (hasDerivAt_neg t) using 1
      simp
    exact ⟨fun s => u (-s), heq, fun s => hupper (-s), hd.differentiableAt,
      by rw [hd.deriv]; linarith⟩)
  simpa only [neg_neg, neg_sub_neg] using h

end Poincare.AncientVolume

universe u

namespace PoincareMT.RicciFlow

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
  {J : Set ℝ}

/-- Ricci upper bounds on current metric balls give a length-independent
additive time-distance bound. Distance continuity and its one-sided slope
bound are produced from the actual flow. -/
theorem toReal_edist_le_add_of_ricci_upper_on_balls_intrinsic
    (F : RicciFlow (m + 1) M J) (hm : 0 < m)
    {a b Λ scale : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection t).ricci x v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hlocal : ∀ t ∈ Icc a b, ∃ r : ℝ, x ∈ (F.metric t).ball p r ∧
      ∀ y ∈ (F.metric t).ball p r, ∀ v : TangentSpace (𝓡 (m + 1)) y,
        (F.connection t).ricci y v v ≤ Λ * (F.metric t).inner y v v) :
    ((F.metric a).edist p x).toReal ≤ ((F.metric b).edist p x).toReal +
      (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (b - a) := by
  by_cases hpx : p = x
  · subst x
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero, zero_add]
    positivity
  have hjoint := F.continuousOn_toReal_edist_of_ricci_nonneg_intrinsic hJ
    (hcomplete b ⟨hab, le_rfl⟩) hRic p
  have hcont : ContinuousOn (fun t => ((F.metric t).edist p x).toReal) (Icc a b) :=
    hjoint.comp (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, mem_univ x⟩)
  apply Poincare.AncientVolume.backward_image_le_add_of_upper_supports hab hcont
  intro t ht
  obtain ⟨r, hx, hupper⟩ := hlocal t (Ioc_subset_Icc_self ht)
  obtain ⟨U, rho, _hU, hxU, _hsmooth, heq, habove, _hgrad, _hlap, hd, hder⟩ :=
    F.exists_distance_spacetime_upper_support (hJ (Ioc_subset_Icc_self ht)) hm
      (hcomplete t (Ioc_subset_Icc_self ht)) (hRic t (Ioc_subset_Icc_self ht))
      hΛ hscale p x hx hpx hupper
  exact ⟨fun s => rho s x, heq, fun s => habove s x hxU, hd, hder⟩

/-- Compatibility form of the intrinsic additive distance estimate. -/
theorem toReal_edist_le_add_of_ricci_upper_on_balls
    (hC : RicciFlowCurvatureCalculus.{u}) (F : RicciFlow (m + 1) M J) (hm : 0 < m)
    {a b Λ scale : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection t).ricci x v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hlocal : ∀ t ∈ Icc a b, ∃ r : ℝ, x ∈ (F.metric t).ball p r ∧
      ∀ y ∈ (F.metric t).ball p r, ∀ v : TangentSpace (𝓡 (m + 1)) y,
        (F.connection t).ricci y v v ≤ Λ * (F.metric t).inner y v v) :
    ((F.metric a).edist p x).toReal ≤ ((F.metric b).edist p x).toReal +
      (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (b - a) := by
  exact F.toReal_edist_le_add_of_ricci_upper_on_balls_intrinsic hm hab hJ
    hcomplete hRic hΛ hscale p x hlocal

/-- A fixed terminal control ball supplies the current balls needed by the
additive comparison. The endpoint radius loses an explicit exponential
factor, while the additive coefficient is independent of that radius. -/
theorem toReal_edist_le_add_of_ricci_upper_on_terminal_ball_intrinsic
    (F : RicciFlow (m + 1) M J) (hm : 0 < m)
    {a b Λ scale r R : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection t).ricci x v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (hr : 0 < r)
    (hmargin : 4 * Real.exp (Λ * (b - a)) * r ≤ R) (O : M)
    (hupper : ∀ t ∈ Icc a b, ∀ z ∈ (F.metric b).ball O R,
      ∀ v : TangentSpace (𝓡 (m + 1)) z,
        (F.connection t).ricci z v v ≤ Λ * (F.metric t).inner z v v)
    (x y : M) (hx : x ∈ (F.metric b).ball O r) (hy : y ∈ (F.metric b).ball O r) :
    ((F.metric a).edist x y).toReal ≤ ((F.metric b).edist x y).toReal +
      (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (b - a) := by
  let E := Real.exp (Λ * (b - a))
  have hE : 0 < E := Real.exp_pos _
  have hEone : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hΛ (sub_nonneg.mpr hab))
  have hthree : 3 * r ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hEone hr.le]
  have hxy : ((F.metric b).edist x y).toReal < 2 * r := by
    let := (F.metric b).toMetricSpace
    have hx' : dist x O < r := by
      simpa only [← (F.metric b).toMetricSpace_ball, Metric.mem_ball] using hx
    have hy' : dist O y < r := by
      simpa only [← (F.metric b).toMetricSpace_ball, Metric.mem_ball, dist_comm] using hy
    change dist x y < 2 * r
    linarith [dist_triangle x O y]
  apply F.toReal_edist_le_add_of_ricci_upper_on_balls_intrinsic hm hab hJ hcomplete hRic hΛ hscale x y
  intro t ht
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hcompare := F.edist_le_exp_mul_of_ricci_bound (convex_Icc a b)
    (hJ.trans interior_subset) O r Λ hr hb ht (fun s hs z hz v => by
      rw [abs_of_nonneg (hRic s hs z v)]
      exact hupper s hs z (lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hthree)) v) hx hy
  have hfinite : ENNReal.ofReal (Real.exp (Λ * |t - b|)) * (F.metric b).edist x y ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((F.metric b).edist_ne_top x y)
  have hdist : ((F.metric t).edist x y).toReal ≤
      Real.exp (Λ * |t - b|) * ((F.metric b).edist x y).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      ENNReal.toReal_mono hfinite hcompare
  have hexp : Real.exp (Λ * |t - b|) ≤ E := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hΛ
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
    linarith [ht.1]
  have hdist' : ((F.metric t).edist x y).toReal < 3 * E * r := by
    have hle := hdist.trans (mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg)
    have hlt := mul_lt_mul_of_pos_left hxy hE
    nlinarith
  have hrad : 0 < 3 * E * r := by positivity
  refine ⟨3 * E * r, ?_, ?_⟩
  · change (F.metric t).edist x y < ENNReal.ofReal (3 * E * r)
    rw [← ENNReal.ofReal_toReal ((F.metric t).edist_ne_top x y)]
    exact (ENNReal.ofReal_lt_ofReal_iff hrad).mpr hdist'
  · intro z hz v
    have hzterminal : z ∈ (F.metric b).ball x (3 * E * r) :=
      F.ball_subset_ball_of_ricci_nonneg hJ x (3 * E * r) ht hb ht.2
        (fun s hs w _ wv => hRic s hs w wv) hz
    have hzcontrol : z ∈ (F.metric b).ball O R := by
      let := (F.metric b).toMetricSpace
      have hx' : dist x O < r := by
        simpa only [← (F.metric b).toMetricSpace_ball, Metric.mem_ball] using hx
      have hz' : dist z x < 3 * E * r := by
        simpa only [← (F.metric b).toMetricSpace_ball, Metric.mem_ball] using hzterminal
      rw [← (F.metric b).toMetricSpace_ball, Metric.mem_ball]
      have hsmall : r + 3 * E * r ≤ R := by
        change 4 * E * r ≤ R at hmargin
        nlinarith [mul_le_mul_of_nonneg_right hEone hr.le]
      linarith [dist_triangle z x O]
    exact hupper t ht z hzcontrol v

/-- Compatibility form of the intrinsic terminal-ball distance estimate. -/
theorem toReal_edist_le_add_of_ricci_upper_on_terminal_ball
    (hC : RicciFlowCurvatureCalculus.{u}) (F : RicciFlow (m + 1) M J) (hm : 0 < m)
    {a b Λ scale r R : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection t).ricci x v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (hr : 0 < r)
    (hmargin : 4 * Real.exp (Λ * (b - a)) * r ≤ R) (O : M)
    (hupper : ∀ t ∈ Icc a b, ∀ z ∈ (F.metric b).ball O R,
      ∀ v : TangentSpace (𝓡 (m + 1)) z,
        (F.connection t).ricci z v v ≤ Λ * (F.metric t).inner z v v)
    (x y : M) (hx : x ∈ (F.metric b).ball O r) (hy : y ∈ (F.metric b).ball O r) :
    ((F.metric a).edist x y).toReal ≤ ((F.metric b).edist x y).toReal +
      (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (b - a) := by
  exact F.toReal_edist_le_add_of_ricci_upper_on_terminal_ball_intrinsic hm hab hJ
    hcomplete hRic hΛ hscale hr hmargin O hupper x y hx hy

end PoincareMT.RicciFlow
