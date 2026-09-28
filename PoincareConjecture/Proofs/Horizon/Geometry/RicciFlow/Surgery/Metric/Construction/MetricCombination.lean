import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.MetricSurgery

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem metric_inner_nonneg (g : RiemannianMetric n M)
    (x : M) (v : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

noncomputable def positiveScaling (g : RiemannianMetric n M) (f : M → ℝ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) :
    RiemannianMetric n M where
  inner x := f x • g.inner x
  symm x v w := by
    change f x * g.inner x v w = f x * g.inner x w v
    rw [g.symm]
  pos x v hv := mul_pos (hpos x) (g.pos x v hv)
  isVonNBounded x := by
    let r := Real.sqrt (f x)
    have hr : 0 < r := Real.sqrt_pos.mpr (hpos x)
    have hr2 : r ^ 2 = f x := Real.sq_sqrt (hpos x).le
    let L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
      r⁻¹ • ContinuousLinearMap.id ℝ _
    refine ((g.isVonNBounded x).image L).subset ?_
    intro v hv
    refine ⟨r • v, ?_, ?_⟩
    · change g.inner x (r • v) (r • v) < 1
      change f x * g.inner x v v < 1 at hv
      calc
        g.inner x (r • v) (r • v) = r ^ 2 * g.inner x v v := by
          simp only [map_smul, smul_apply, smul_eq_mul]
          ring
        _ = f x * g.inner x v v := by rw [hr2]
        _ < 1 := hv
    · change r⁻¹ • (r • v) = v
      simp [smul_smul, hr.ne']
  contMDiff := hf.smul_section g.contMDiff

theorem positiveScaling_inner (g : RiemannianMetric n M) (f : M → ℝ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (positiveScaling g f hf hpos).inner x v w = f x * g.inner x v w := rfl

noncomputable def convexCombination (g h : RiemannianMetric n M) (a : M → ℝ)
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hweight : ∀ x, 0 ≤ a x ∧ a x ≤ 1) : RiemannianMetric n M where
  inner x := a x • g.inner x + (1 - a x) • h.inner x
  symm x v w := by
    change a x * g.inner x v w + (1 - a x) * h.inner x v w =
      a x * g.inner x w v + (1 - a x) * h.inner x w v
    rw [g.symm, h.symm]
  pos x v hv := by
    change 0 < a x * g.inner x v v + (1 - a x) * h.inner x v v
    by_cases hx : (1 / 2 : ℝ) ≤ a x
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (by linarith) (g.pos x v hv))
        (mul_nonneg (sub_nonneg.mpr (hweight x).2) (metric_inner_nonneg h x v))
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (hweight x).1 (metric_inner_nonneg g x v))
        (mul_pos (by linarith) (h.pos x v hv))
  isVonNBounded x := by
    by_cases hx : (1 / 2 : ℝ) ≤ a x
    · let ref := positiveScaling g (fun _ => 1 / 2) contMDiff_const (by
        intro _
        norm_num)
      refine (ref.isVonNBounded x).subset ?_
      intro v hv
      change (1 / 2 : ℝ) * g.inner x v v < 1
      change a x * g.inner x v v + (1 - a x) * h.inner x v v < 1 at hv
      have hg := mul_nonneg (sub_nonneg.mpr hx) (metric_inner_nonneg g x v)
      have hh := mul_nonneg (sub_nonneg.mpr (hweight x).2) (metric_inner_nonneg h x v)
      nlinarith
    · let ref := positiveScaling h (fun _ => 1 / 2) contMDiff_const (by
        intro _
        norm_num)
      refine (ref.isVonNBounded x).subset ?_
      intro v hv
      change (1 / 2 : ℝ) * h.inner x v v < 1
      change a x * g.inner x v v + (1 - a x) * h.inner x v v < 1 at hv
      have hg := mul_nonneg (hweight x).1 (metric_inner_nonneg g x v)
      have hh := mul_nonneg (by linarith : 0 ≤ 1 / 2 - a x)
        (metric_inner_nonneg h x v)
      nlinarith
  contMDiff := (ha.smul_section g.contMDiff).add_section
    ((contMDiff_const.sub ha).smul_section h.contMDiff)

theorem convexCombination_inner (g h : RiemannianMetric n M) (a : M → ℝ)
    (ha : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ a)
    (hweight : ∀ x, 0 ≤ a x ∧ a x ≤ 1)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (convexCombination g h a ha hweight).inner x v w =
      a x * g.inner x v w + (1 - a x) * h.inner x v w := rfl

end PoincareConjecture.MetricSurgery
