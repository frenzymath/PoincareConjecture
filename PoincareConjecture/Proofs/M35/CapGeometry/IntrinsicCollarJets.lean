import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicShapeDerivative
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicCollarRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

theorem intrinsic_orbit_sq_deriv {s : ℝ} (hs : 0 < s) :
    deriv (fun u => intrinsicWarpingRadius g hrotation hcomplete u ^ 2) s =
      2 * intrinsicRadialShape g hrotation hcomplete s *
        intrinsicWarpingRadius g hrotation hcomplete s ^ 2 := by
  have hf := (intrinsicWarpingRadius_contDiff g hrotation hcomplete).differentiable
    (by simp) s
  rw [(hf.hasDerivAt.fun_pow 2).deriv]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, intrinsicRadialShape]
  field_simp [(intrinsicWarpingRadius_pos g hrotation hcomplete hs).ne']

theorem intrinsic_orbit_sq_jets_tendsto
    (g : ℕ → RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ k, ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (g k).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (g k).inner x u v)
    (hcomplete : ∀ k, MetricComplete (g k)) (b : ℕ → ℝ)
    (hb : ∀ᶠ k in atTop, 0 < b k)
    (hvalue : Tendsto (fun k =>
      intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k) (b k) ^ 2) atTop (𝓝 2))
    (hshape : ∀ m : ℕ, Tendsto (fun k => iteratedDeriv m
      (intrinsicRadialShape (g k) (hrotation k) (hcomplete k)) (b k)) atTop (𝓝 0)) :
    ∀ m : ℕ, Tendsto (fun k => iteratedDeriv m
      (fun s => intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k) s ^ 2) (b k))
        atTop (𝓝 (if m = 0 then 2 else 0)) := by
  let A k s := intrinsicWarpingRadius (g k) (hrotation k) (hcomplete k) s ^ 2
  let S k := intrinsicRadialShape (g k) (hrotation k) (hcomplete k)
  have hA k : ContDiff ℝ ∞ (A k) :=
    (intrinsicWarpingRadius_contDiff (g k) (hrotation k) (hcomplete k)).pow 2
  intro m
  induction m using Nat.strong_induction_on with
  | h m hm =>
    cases m with
    | zero => simpa only [iteratedDeriv_zero, if_true] using hvalue
    | succ n =>
      have hterm (j : ℕ) (_hj : j ∈ Finset.range (n + 1)) :
          Tendsto (fun k => (n.choose j : ℝ) * iteratedDeriv j (S k) (b k) *
            iteratedDeriv (n - j) (A k) (b k)) atTop (𝓝 0) := by
        have hh := ((hshape j).const_mul (n.choose j : ℝ)).mul
          (hm (n - j) (Nat.lt_succ_of_le (Nat.sub_le n j)))
        simpa only [mul_zero, zero_mul] using hh
      have hsum : Tendsto (fun k => 2 * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * iteratedDeriv j (S k) (b k) *
            iteratedDeriv (n - j) (A k) (b k)) atTop (𝓝 0) := by
        simpa only [Finset.sum_const_zero, mul_zero] using
          (tendsto_finsetSum (Finset.range (n + 1)) hterm).const_mul 2
      have heq : ∀ᶠ k in atTop, iteratedDeriv (n + 1) (A k) (b k) =
          2 * ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
            iteratedDeriv j (S k) (b k) * iteratedDeriv (n - j) (A k) (b k) := by
        filter_upwards [hb] with k hk
        have hlocal : deriv (A k) =ᶠ[𝓝 (b k)] (fun s => 2 * (S k s * A k s)) := by
          filter_upwards [eventually_gt_nhds hk] with s hs
          have h := intrinsic_orbit_sq_deriv (g k) (hrotation k) (hcomplete k) hs
          simpa only [A, S, mul_assoc] using h
        rw [iteratedDeriv_succ', hlocal.iteratedDeriv_eq n, iteratedDeriv_const_mul_field]
        have hn : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (n : ℕ∞))
        rw [iteratedDeriv_fun_mul
          ((intrinsicRadialShape_contDiffAt (g k) (hrotation k) (hcomplete k) hk).of_le hn)
          ((hA k).contDiffAt.of_le hn)]
      simpa only [Nat.succ_ne_zero, if_false] using
        hsum.congr' (heq.mono fun _ h => h.symm)

end PoincareConjecture.M35.Uniqueness
