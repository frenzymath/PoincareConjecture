import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*}

theorem conjugateHeatDensity_pos (f : M × ℝ → ℝ) {t : ℝ} (ht : t < 0)
    (x : M) : 0 < conjugateHeatDensity n f t x :=
  mul_pos (Real.rpow_pos_of_pos (neg_pos.mpr ht) _) (Real.exp_pos _)

theorem hasDerivAt_conjugateHeatDensity {f : M × ℝ → ℝ} {t a : ℝ}
    (ht : t < 0) (x : M) (hf : HasDerivAt (fun s ↦ f (x, s)) a t) :
    HasDerivAt (fun s ↦ conjugateHeatDensity n f s x)
      ((n / (2 * -t) - a) * conjugateHeatDensity n f t x) t := by
  have hb := ((hasDerivAt_id t).neg).rpow_const
    (p := -(n : ℝ) / 2) (Or.inl (ne_of_gt (neg_pos.mpr ht)))
  convert! hb.mul hf.neg.exp using 1
  simp only [conjugateHeatDensity, id, Pi.neg_apply, Real.rpow_eq_pow]
  rw [Real.rpow_sub (neg_pos.mpr ht), Real.rpow_one]
  field_simp
  ring

namespace LeviCivitaData

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

theorem laplacian_exp_neg (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    D.laplacian (fun y ↦ Real.exp (-f y)) x =
      Real.exp (-f x) * (g.inner x (D.gradient f x) (D.gradient f x) -
        D.laplacian f x) := by
  have hd : deriv (fun a : ℝ ↦ Real.exp (-a)) = fun a ↦ -Real.exp (-a) := by
    funext a
    simpa using ((hasDerivAt_id a).neg.exp).deriv
  have hdd (a : ℝ) : deriv (fun b : ℝ ↦ -Real.exp (-b)) a = Real.exp (-a) := by
    simpa using ((hasDerivAt_id a).neg.exp.neg).deriv
  have he : ContDiff ℝ ∞ (fun a : ℝ ↦ Real.exp (-a)) :=
    Real.contDiff_exp.comp contDiff_id.neg
  have h := D.laplacian_comp hf he x
  rw [hd, hdd] at h
  change D.laplacian (fun y ↦ Real.exp (-f y)) x = _ at h
  rw [h]
  ring

theorem gradient_exp_neg (D : LeviCivitaData g) {f : M → ℝ}
    {x : M} (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) :
    D.gradient (fun y ↦ Real.exp (-f y)) x =
      -Real.exp (-f x) • D.gradient f x := by
  have hd : HasDerivAt (fun a : ℝ ↦ Real.exp (-a)) (-Real.exp (-f x)) (f x) := by
    simpa using ((hasDerivAt_id (f x)).neg.exp)
  simpa only [Function.comp_def, hd.deriv] using
    D.gradient_comp hf hd.differentiableAt

end LeviCivitaData

namespace RicciFlow

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}

theorem gradient_conjugateHeatDensity (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ f (y, t)) x) :
    (F.connection t).gradient (conjugateHeatDensity n f t) x =
      -conjugateHeatDensity n f t x •
        (F.connection t).gradient (fun y ↦ f (y, t)) x := by
  apply ((F.metric t).inner_isInvertible x).injective
  ext v
  rw [(F.connection t).inner_gradient]
  unfold conjugateHeatDensity
  rw [mvfderiv_const_mul, ← (F.connection t).inner_gradient,
    (F.connection t).gradient_exp_neg hf]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem laplacian_conjugateHeatDensity (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (y, t))) (x : M) :
    (F.connection t).laplacian (conjugateHeatDensity n f t) x =
      conjugateHeatDensity n f t x *
        ((F.metric t).inner x ((F.connection t).gradient (fun y ↦ f (y, t)) x)
          ((F.connection t).gradient (fun y ↦ f (y, t)) x) -
          (F.connection t).laplacian (fun y ↦ f (y, t)) x) := by
  unfold conjugateHeatDensity
  rw [(F.connection t).laplacian_const_mul,
    (F.connection t).laplacian_exp_neg hf]
  ring

theorem conjugateHeatDensity_residual (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ} (ht : t < 0)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (y, t)))
    (x : M) (hft : DifferentiableAt ℝ (fun s ↦ f (x, s)) t) :
    F.conjugateHeatResidual (fun z ↦ conjugateHeatDensity n f z.2 z.1) t x =
        -conjugateHeatDensity n f t x * F.potentialResidual f t x := by
  unfold conjugateHeatResidual
  rw [(hasDerivAt_conjugateHeatDensity ht x hft.hasDerivAt).deriv,
    F.laplacian_conjugateHeatDensity hf]
  dsimp only [potentialResidual]
  ring

theorem conjugateHeatDensity_residual_eq_zero_iff (F : RicciFlow n M J)
    {f : M × ℝ → ℝ} {t : ℝ} (ht : t < 0)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ f (y, t)))
    (x : M) (hft : DifferentiableAt ℝ (fun s ↦ f (x, s)) t) :
    F.conjugateHeatResidual (fun z ↦ conjugateHeatDensity n f z.2 z.1) t x = 0 ↔
      F.potentialResidual f t x = 0 := by
  rw [F.conjugateHeatDensity_residual ht hf x hft, mul_eq_zero]
  simp only [neg_ne_zero.mpr (ne_of_gt (conjugateHeatDensity_pos f ht x)), false_or]

end RicciFlow

end PoincareConjecture
