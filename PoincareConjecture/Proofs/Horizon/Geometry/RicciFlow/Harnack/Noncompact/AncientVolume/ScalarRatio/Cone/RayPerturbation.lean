import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RayLimits

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

open Splitting (segmentComparisonCosine)

private theorem tendsto_scaled_ray_error
    {X : Type*} [MetricSpace X] (ray : ℝ → X)
    (hray : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (ray s) (ray t) = |s - t|)
    (scale a : ℕ → ℝ) (hscale : ∀ i, 0 < scale i) (ha : ∀ i, 0 ≤ a i)
    (x : ℕ → X) {r : ℝ} (hr : 0 < r)
    (hrad : Tendsto (fun i => scale i * a i) atTop (𝓝 r))
    (herr : Tendsto (fun i => scale i * dist (x i) (ray (a i))) atTop (𝓝 0)) :
    Tendsto (fun i => scale i * dist (x i) (ray (r / scale i))) atTop (𝓝 0) := by
  have hradError : Tendsto (fun i => |scale i * a i - r|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hrad.sub_const r).abs
  apply squeeze_zero (fun i => mul_nonneg (hscale i).le dist_nonneg) _
    (by simpa only [zero_add] using herr.add hradError)
  intro i
  have htriangle := mul_le_mul_of_nonneg_left
    (dist_triangle (x i) (ray (a i)) (ray (r / scale i))) (hscale i).le
  have hradial : scale i * dist (ray (a i)) (ray (r / scale i)) = |scale i * a i - r| := by
    rw [hray (a i) (ha i) (r / scale i) (div_nonneg hr.le (hscale i).le)]
    calc
      scale i * |a i - r / scale i| = |scale i * (a i - r / scale i)| := by
        rw [abs_mul, abs_of_pos (hscale i)]
      _ = |scale i * a i - r| := by congr 1; field_simp [(hscale i).ne']
  rw [mul_add, hradial] at htriangle
  exact htriangle

private theorem tendsto_scaled_distance_of_homogeneous_ray_limit
    {X : Type*} [MetricSpace X] (α β : ℝ → X)
    (hα : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (α s) (α t) = |s - t|)
    (hβ : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (β s) (β t) = |s - t|)
    (scale a b : ℕ → ℝ) (hscale : ∀ i, 0 < scale i)
    (hscalezero : Tendsto scale atTop (𝓝 0)) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (x y : ℕ → X) {r s D : ℝ} (hr : 0 < r) (hs : 0 < s)
    (har : Tendsto (fun i => scale i * a i) atTop (𝓝 r))
    (hbs : Tendsto (fun i => scale i * b i) atTop (𝓝 s))
    (hx : Tendsto (fun i => scale i * dist (x i) (α (a i))) atTop (𝓝 0))
    (hy : Tendsto (fun i => scale i * dist (y i) (β (b i))) atTop (𝓝 0))
    (hlimit : Tendsto (fun L : ℝ => dist (α (r * L)) (β (s * L)) / L)
      atTop (𝓝 D)) :
    Tendsto (fun i => scale i * dist (x i) (y i)) atTop (𝓝 D) := by
  have hinv : Tendsto (fun i => (scale i)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hscalezero, Eventually.of_forall hscale⟩)
  have hfixed : Tendsto (fun i => scale i * dist (α (r / scale i)) (β (s / scale i)))
      atTop (𝓝 D) := by
    convert! hlimit.comp hinv using 1
    funext i
    simp only [Function.comp_apply, div_eq_mul_inv, inv_inv]
    ring
  have hx' := tendsto_scaled_ray_error α hα scale a hscale ha x hr har hx
  have hy' := tendsto_scaled_ray_error β hβ scale b hscale hb y hs hbs hy
  apply hfixed.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _
    (by simpa only [zero_add] using hx'.add hy')
  intro i
  have hd := mul_le_mul_of_nonneg_left
    (dist_dist_dist_le (α (r / scale i)) (β (s / scale i)) (x i) (y i)) (hscale i).le
  calc
    dist (scale i * dist (α (r / scale i)) (β (s / scale i)))
        (scale i * dist (x i) (y i)) =
        scale i * dist (dist (α (r / scale i)) (β (s / scale i))) (dist (x i) (y i)) := by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (hscale i), Real.dist_eq]
    _ ≤ scale i * (dist (α (r / scale i)) (x i) + dist (β (s / scale i)) (y i)) := hd
    _ = scale i * dist (x i) (α (r / scale i)) +
        scale i * dist (y i) (β (s / scale i)) := by
      rw [mul_add, dist_comm (α (r / scale i)) (x i), dist_comm (β (s / scale i)) (y i)]

theorem tendsto_radial_perturbation_sq_of_ray_approximation
    {X : Type*} [MetricSpace X] (α β : ℝ → X) (hzero : α 0 = β 0)
    (hα : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (α s) (α t) = |s - t|)
    (hβ : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (β s) (β t) = |s - t|)
    (hcomparison : ∀ a b : ℝ, 0 < a → 0 < b →
      ∀ u ∈ Icc (0 : ℝ) a, ∀ v ∈ Icc (0 : ℝ) b,
        u ^ 2 + v ^ 2 - 2 * u * v * segmentComparisonCosine α β a b ≤
          dist (α u) (β v) ^ 2)
    (scale a b : ℕ → ℝ) (hscale : ∀ i, 0 < scale i)
    (hscalezero : Tendsto scale atTop (𝓝 0)) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (x z : ℕ → X) {r s D : ℝ} (hr : 0 < r) (hs : 0 < s)
    (har : Tendsto (fun i => scale i * a i) atTop (𝓝 r))
    (hbs : Tendsto (fun i => scale i * b i) atTop (𝓝 s))
    (hx : Tendsto (fun i => scale i * dist (x i) (α (a i))) atTop (𝓝 0))
    (hz : Tendsto (fun i => scale i * dist (z i) (β (b i))) atTop (𝓝 0))
    (hxz : Tendsto (fun i => scale i * dist (x i) (z i)) atTop (𝓝 D)) :
    ∀ c : ℝ, 0 < c →
      Tendsto (fun i => (scale i * dist (x i) (β (c * b i))) ^ 2)
        atTop (𝓝 (c ^ 2 * s ^ 2 + r ^ 2 - c * (s ^ 2 + r ^ 2 - D ^ 2))) := by
  obtain ⟨q, hq, hlimits⟩ := exists_homogeneous_ray_distance_limit
    α β hzero hα hβ hcomparison
  have hbase := tendsto_scaled_distance_of_homogeneous_ray_limit α β hα hβ
    scale a b hscale hscalezero ha hb x z hr hs har hbs hx hz (hlimits r s hr hs).2
  have hqnorm : 0 ≤ r ^ 2 + s ^ 2 - 2 * r * s * q := by
    have hh := mul_le_mul_of_nonneg_left hq.2 (by positivity : 0 ≤ 2 * r * s)
    nlinarith [sq_nonneg (r - s)]
  have hD : D ^ 2 = r ^ 2 + s ^ 2 - 2 * r * s * q := by
    rw [tendsto_nhds_unique hxz hbase, Real.sq_sqrt hqnorm]
  intro c hc
  have hb' : Tendsto (fun i => scale i * (c * b i)) atTop (𝓝 (c * s)) := by
    convert! hbs.const_mul c using 1
    funext i
    ring
  have hz' : Tendsto (fun i => scale i * dist (β (c * b i)) (β (c * b i))) atTop (𝓝 0) := by
    simp only [dist_self, mul_zero]
    exact tendsto_const_nhds
  have hnew := tendsto_scaled_distance_of_homogeneous_ray_limit α β hα hβ
    scale a (fun i => c * b i) hscale hscalezero ha (fun i => mul_nonneg hc.le (hb i))
    x (fun i => β (c * b i)) hr (mul_pos hc hs) har hb' hx hz'
    (hlimits r (c * s) hr (mul_pos hc hs)).2
  have hnonneg : 0 ≤ r ^ 2 + (c * s) ^ 2 - 2 * r * (c * s) * q := by
    have hh := mul_le_mul_of_nonneg_left hq.2 (by positivity : 0 ≤ 2 * r * (c * s))
    nlinarith [sq_nonneg (r - c * s)]
  have heq : (Real.sqrt (r ^ 2 + (c * s) ^ 2 - 2 * r * (c * s) * q)) ^ 2 =
      c ^ 2 * s ^ 2 + r ^ 2 - c * (s ^ 2 + r ^ 2 - D ^ 2) := by
    rw [Real.sq_sqrt hnonneg, hD]
    ring
  simpa only [heq] using hnew.pow 2

end Poincare.AncientVolume.ScalarRatio
