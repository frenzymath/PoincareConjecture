import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem intrinsic_collar_orbit_sq_tendsto_two
    (g : ℕ → RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ k, ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (g k).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (g k).inner x u v)
    (hcomplete : ∀ k, MetricComplete (g k)) (D : ∀ k, LeviCivitaData (g k))
    (hsec : ∀ k, (D k).NonnegativeSectionalCurvature)
    (a b : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (hcenter : Tendsto (fun k =>
      intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k) (a k) ^ 2) atTop (𝓝 2))
    {L : ℝ} (hL : 0 ≤ L) (hcollar : ∀ᶠ k in atTop, |b k - a k| ≤ L) :
    Tendsto (fun k => intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k) (b k) ^ 2)
      atTop (𝓝 2) := by
  let f k := intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k)
  have hroot : Tendsto (fun k => f k (a k)) atTop (𝓝 (Real.sqrt 2)) := by
    have h := (Real.continuous_sqrt.tendsto 2).comp hcenter
    apply h.congr'
    filter_upwards [ha.eventually (eventually_gt_atTop 0)] with k hk
    exact Real.sqrt_sq (intrinsicWarpingRadius_pos (g k) (hrotation k) (hcomplete k) hk).le
  have hratio : Tendsto (fun k => f k (a k) / a k) atTop (𝓝 0) := hroot.div_atTop ha
  have hbound : ∀ᶠ k in atTop, |f k (b k) - f k (a k)| ≤ f k (a k) / a k * L := by
    filter_upwards [ha.eventually (eventually_gt_atTop (L + 1)), hcollar] with k hk hc
    have hak : 0 < a k := lt_trans (by positivity : (0 : ℝ) < L + 1) hk
    have hbk : 0 < b k := by linarith [(abs_le.mp hc).1]
    exact (intrinsicWarpingRadius_anchored_variation (g k) (hrotation k) (hcomplete k)
      (D k) (hsec k) hak hbk).trans (mul_le_mul_of_nonneg_left hc
        (div_nonneg (intrinsicWarpingRadius_pos (g k) (hrotation k) (hcomplete k) hak).le hak.le))
  have hdiff : Tendsto (fun k => f k (b k) - f k (a k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hbound)
    simpa only [zero_mul] using hratio.mul_const L
  have hf : Tendsto (fun k => f k (b k)) atTop (𝓝 (Real.sqrt 2)) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add hroot
  simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hf.pow 2

end PoincareConjecture.M35.Uniqueness
