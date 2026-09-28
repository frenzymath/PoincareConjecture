import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Ray
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Hessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Global
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_squared_distance_quadratic_concave
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {curve : ℝ → M} {a b : ℝ} (hab : a < b)
    (hcurve : g.IsGeodesicOn curve (Icc a b)) :
    ∃ C : ℝ≥0, ∀ p : M, ConcaveOn ℝ (Icc a b)
      (fun t => (g.edist p (curve t)).toReal ^ 2 - (C : ℝ) ^ 2 * t ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcurve' : g.IsGeodesicOn curve (Ioo a b) := fun t ht =>
    hcurve t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨C, hC⟩ := hcurve'.exists_constant_tangentNorm hab
  refine ⟨C, fun p => ?_⟩
  have hcontinuous : ContinuousOn curve (Icc a b) := fun t ht =>
    (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hcurve ht).continuousAt.continuousWithinAt
  apply Poincare.Analysis.concaveOn_sub_quadratic_of_approximate_upper_support
    (((g.continuous_toReal_edist p).comp_continuousOn hcontinuous).pow 2)
  intro t ht ε hε
  have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  by_cases hpx : p = curve t
  · refine ⟨fun s => (C : ℝ) ^ 2 * (s - t) ^ 2, by fun_prop, ?_, ?_, ?_⟩
    · have hself : g.edist (curve t) (curve t) = 0 := by
        apply le_antisymm
        · simpa only [edist_dist, dist_self, ENNReal.ofReal_zero, mul_zero] using
            hcurve'.edist_le_of_tangentNorm_eq hC ht ht
        · exact bot_le
      change (C : ℝ) ^ 2 * (t - t) ^ 2 = (g.edist p (curve t)).toReal ^ 2
      simp [hpx, hself]
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      have hd := hcurve'.edist_le_of_tangentNorm_eq hC ht hs
      have hd' := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (_root_.edist_ne_top t s)) hd
      simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
        Real.dist_eq, abs_sub_comm t s, ENNReal.toReal_ofReal (abs_nonneg _)] at hd'
      rw [hpx]
      calc
        (g.edist (curve t) (curve s)).toReal ^ 2 ≤ ((C : ℝ) * |s - t|) ^ 2 :=
          pow_le_pow_left₀ ENNReal.toReal_nonneg hd' 2
        _ = (C : ℝ) ^ 2 * (s - t) ^ 2 := by rw [mul_pow, sq_abs]
    · have hfirst : deriv (fun s : ℝ => (C : ℝ) ^ 2 * (s - t) ^ 2) =
          fun s => (C : ℝ) ^ 2 * (2 * (s - t)) := by
        funext s
        convert! ((((hasDerivAt_id s).sub_const t).pow 2).const_mul ((C : ℝ) ^ 2)).deriv using 1
        simp
      have hsecond := ((((hasDerivAt_id t).sub_const t).const_mul 2).const_mul
        ((C : ℝ) ^ 2)).deriv
      simp only [id_eq] at hsecond
      rw [hfirst, hsecond]
      linarith
  · obtain ⟨u, hu, htouch, hmajor, hbound⟩ :=
      g.exists_squared_distance_upper_support D hcomplete hsec p hcurve htcc hpx hε
    have hnonneg : 0 ≤ g.inner (curve t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1) := by
      by_cases hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) curve t 1 = 0
      · simp [hv]
      · exact (g.pos _ _ hv).le
    have hsquared := congrArg (fun x : ℝ => x ^ 2) (hC t ht)
    rw [tangentNorm, Real.sq_sqrt hnonneg] at hsquared
    exact ⟨u, hu, htouch, hmajor, by simpa only [hsquared] using hbound⟩

end PoincareConjecture.RiemannianMetric

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

theorem tendsto_normalized_squared_distance {ray : ℝ → M} (hray : IsRay ray)
    (x : M) (A : ℝ) :
    Tendsto (fun T : ℝ => (dist (ray T) x ^ 2 - A - T ^ 2) / (2 * T)) atTop
      (𝓝 (busemann ray x)) := by
  have hb := tendsto_busemannApprox hray x
  have hzero : Tendsto (fun T : ℝ =>
      ((busemannApprox ray T x) ^ 2 - A) * T⁻¹ / 2) atTop (𝓝 0) := by
    simpa using (((hb.pow 2).sub (tendsto_const_nhds (x := A))).mul
      tendsto_inv_atTop_zero).div_const 2
  have hsum := hb.add hzero
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  dsimp [busemannApprox]
  field_simp [hT.ne']
  ring

end Poincare.Riemannian.Soul

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian.Soul

variable {n : ℕ} {M : Type*} [MetricSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem concaveOn_busemann_of_nonnegativeSectional
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray curve : ℝ → M} (hray : IsRay ray) {a b : ℝ}
    (hcurve : g.IsGeodesicOn curve (Icc a b)) :
    ConcaveOn ℝ (Icc a b) (Poincare.Riemannian.Soul.busemann ray ∘ curve) := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy α β hα hβ hsum
  simp only [Function.comp_apply, smul_eq_mul]
  by_cases hab : a < b
  · obtain ⟨C, hC⟩ := g.exists_squared_distance_quadratic_concave D hcomplete hsec hab hcurve
    have hleft :=
      ((tendsto_normalized_squared_distance hray (curve x) ((C : ℝ) ^ 2 * x ^ 2)).const_mul α).add
        ((tendsto_normalized_squared_distance hray (curve y) ((C : ℝ) ^ 2 * y ^ 2)).const_mul β)
    have hright := tendsto_normalized_squared_distance hray (curve (α * x + β * y))
      ((C : ℝ) ^ 2 * (α * x + β * y) ^ 2)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have h := (hC (ray T)).2 hx hy hα hβ hsum
    simp only [smul_eq_mul] at h
    simp only [hdist]
    apply (le_div_iff₀ (by positivity : 0 < 2 * T)).2
    field_simp [hT.ne']
    nlinarith
  · have hxa : x = a := by linarith [hx.1, hx.2]
    have hya : y = a := by linarith [hy.1, hy.2]
    have hcomb : α * x + β * y = a := by rw [hxa, hya, ← add_mul, hsum, one_mul]
    rw [hcomb, hxa, hya, ← add_mul, hsum, one_mul]

end PoincareConjecture.RiemannianMetric
