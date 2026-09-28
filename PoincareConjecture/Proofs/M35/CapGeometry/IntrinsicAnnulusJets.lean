import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicCollarJets
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCylinderJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness



theorem intrinsic_annulus_jetError_tendsto_zero
    (g : ℕ → RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ k, ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (g k).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (g k).inner x u v)
    (hcomplete : ∀ k, MetricComplete (g k)) (a b s : ℕ → ℝ)
    (s₀ : ℝ) (q : ℕ → UnitTwoSphere) (order : ℕ)
    (hb : Tendsto b atTop (𝓝 1)) (hs : Tendsto s atTop (𝓝 s₀))
    (hjet : ∀ m : ℕ, Tendsto (fun k => iteratedDeriv m
      (fun r => intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k) r ^ 2)
        (a k + b k * s k)) atTop (𝓝 (if m = 0 then 2 else 0))) :
    Tendsto (fun k => roundCylinderJetErrorSquared 0
      (radialCylinderTensor
        (fun u => intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k)
          (a k + b k * u) ^ 2) (b k)) order (q k, s k)) atTop (𝓝 0) := by
  let A k r := intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k) r ^ 2
  let B k u := A k (a k + b k * u)
  have hA (k : ℕ) : ContDiff ℝ ∞ (A k) :=
    (intrinsicWarpingRadius_contDiff (g k) (hrotation k) (hcomplete k)).pow 2
  have hB (k : ℕ) : ContDiff ℝ ∞ (B k) :=
    (hA k).comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hformula (m k : ℕ) : iteratedDeriv m (B k) (s k) =
      b k ^ m * iteratedDeriv m (A k) (a k + b k * s k) := by
    have hm : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (m : ℕ∞))
    have hc : ContDiff ℝ m (fun u => A k (a k + u)) :=
      ((hA k).comp (contDiff_const.add contDiff_id)).of_le hm
    have h := congrFun (iteratedDeriv_comp_const_mul hc (b k)) (s k)
    rw [iteratedDeriv_comp_const_add] at h
    exact h
  have hBjet (m : ℕ) : Tendsto (fun k => iteratedDeriv m (B k) (s k))
      atTop (𝓝 (if m = 0 then 2 else 0)) := by
    simp_rw [hformula]
    simpa only [one_pow, one_mul] using (hb.pow m).mul (hjet m)
  have herr (m : ℕ) : Tendsto
      (fun k => iteratedDeriv m (fun u => B k u - 2) (s k)) atTop (𝓝 0) := by
    have hm : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (m : ℕ∞))
    have heq (k : ℕ) : iteratedDeriv m (fun u => B k u - 2) (s k) =
        iteratedDeriv m (B k) (s k) - (if m = 0 then 2 else 0) := by
      rw [iteratedDeriv_fun_sub ((hB k).contDiffAt.of_le hm) contDiffAt_const,
        iteratedDeriv_const]
    simp_rw [heq]
    simpa only [sub_self] using (hBjet m).sub_const (if m = 0 then 2 else 0)
  apply radialCylinderTensor_jetError_tendsto_zero B b s s₀ q order hs hb
    (fun k => (hB k).contDiffAt)
  intro m _hm
  have h := ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).continuous.tendsto 0).comp
    (herr m)
  simpa only [iteratedFDeriv_eq_equiv_comp, Function.comp_def, map_zero] using h

end PoincareConjecture.M35.Uniqueness
