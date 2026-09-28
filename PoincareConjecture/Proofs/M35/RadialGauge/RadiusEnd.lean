import PoincareConjecture.Proofs.M35.RadialGauge.CorrectedEquation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv











set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge



theorem mapRadius_third_deriv {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    deriv (deriv (deriv (mapRadius u))) r =
      Real.exp (u r) * (3 * deriv u r ^ 2 + 3 * deriv (deriv u) r +
        r * (deriv u r ^ 3 + 3 * deriv u r * deriv (deriv u) r +
          deriv (deriv (deriv u)) r)) := by
  have hu1 := (contDiff_infty_iff_deriv.mp hu).2
  have hu2 := (contDiff_infty_iff_deriv.mp hu1).2
  have h0 := (hu.differentiable (by simp) r).hasDerivAt
  have h1 := (hu1.differentiable (by simp) r).hasDerivAt
  have h2 := (hu2.differentiable (by simp) r).hasDerivAt
  have heq : deriv (deriv (mapRadius u)) = fun s =>
      Real.exp (u s) * (2 * deriv u s + s * (deriv u s ^ 2 + deriv (deriv u) s)) :=
    funext (mapRadius_second_deriv hu)
  rw [heq]
  have h := h0.exp.mul ((h1.const_mul 2).add
    ((hasDerivAt_id r).mul ((h1.pow 2).add h2)))
  convert! h.deriv using 1
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul,
    Pi.pow_apply, Pi.add_apply, Pi.mul_apply]
  ring



theorem mapRadius_ratio_tendsto
    {A : Type*} {l : Filter A} {r : A → ℝ} {u : A → ℝ → ℝ}
    (hr : ∀ᶠ a in l, r a ≠ 0)
    (hu : Tendsto (fun a => u a (r a)) l (𝓝 0)) :
    Tendsto (fun a => mapRadius (u a) (r a) / r a) l (𝓝 1) := by
  have h := (Real.continuous_exp.tendsto 0).comp hu
  simp only [Real.exp_zero] at h
  apply h.congr'
  filter_upwards [hr] with a ha
  simp [mapRadius, ha]



theorem mapRadius_deriv_tendsto
    {A : Type*} {l : Filter A} {r : A → ℝ} {u : A → ℝ → ℝ}
    (hsmooth : ∀ a, ContDiff ℝ ∞ (u a))
    (hu : Tendsto (fun a => u a (r a)) l (𝓝 0))
    (hdu : Tendsto (fun a => r a * deriv (u a) (r a)) l (𝓝 0)) :
    Tendsto (fun a => deriv (mapRadius (u a)) (r a)) l (𝓝 1) := by
  have heq (a : A) : deriv (mapRadius (u a)) (r a) =
      Real.exp (u a (r a)) * (1 + r a * deriv (u a) (r a)) :=
    (mapRadius_hasDerivAt (((hsmooth a).differentiable (by simp) (r a)).hasDerivAt)).deriv
  simp_rw [heq]
  simpa only [Function.comp_apply, Real.exp_zero, add_zero, mul_one] using
    ((Real.continuous_exp.tendsto 0).comp hu).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add hdu)




theorem mapRadius_second_deriv_tendsto
    {A : Type*} {l : Filter A} {r : A → ℝ} {u : A → ℝ → ℝ}
    (hsmooth : ∀ a, ContDiff ℝ ∞ (u a))
    (hu : Tendsto (fun a => u a (r a)) l (𝓝 0))
    (hu1 : Tendsto (fun a => deriv (u a) (r a)) l (𝓝 0))
    (hdu1 : Tendsto (fun a => r a * deriv (u a) (r a)) l (𝓝 0))
    (hdu2 : Tendsto (fun a => r a * deriv (deriv (u a)) (r a)) l (𝓝 0)) :
    Tendsto (fun a => deriv (deriv (mapRadius (u a))) (r a)) l (𝓝 0) := by
  have h := ((Real.continuous_exp.tendsto 0).comp hu).mul
    (((tendsto_const_nhds (x := (2 : ℝ))).mul hu1).add
    ((hdu1.mul hu1).add hdu2))
  simp only [Function.comp_apply, Real.exp_zero, mul_zero, zero_add] at h
  convert h using 1
  ext a
  rw [mapRadius_second_deriv (hsmooth a)]
  ring

end PoincareConjecture.M35.RadialGauge
