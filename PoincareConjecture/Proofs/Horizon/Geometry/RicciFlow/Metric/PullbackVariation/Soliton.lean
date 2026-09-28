import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Metric.PullbackVariation
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J) (hJ : IsOpen J)
  {f : ℝ × M → ℝ} {Φ : ℝ → M → M}
  (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (J ×ˢ univ))
  (hs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
    (fun z : ℝ × M => Φ z.1 z.2) (J ×ˢ univ))
  (hΦ : ∀ s ∈ J, ∀ y, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => Φ r y) s
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (-((F.connection s).gradient (fun z => f (s, z)) (Φ s y)))))

include hJ hf hs hΦ



theorem hasDerivAt_soliton_pullback_metric {t : ℝ} (ht : t ∈ J)
    (hsol : ∀ y (a b : TangentSpace (𝓡 n) y),
      (F.connection t).ricci y a b + (F.connection t).hessian (fun z => f (t, z)) y a b +
        (1 / (2 * t)) * (F.metric t).inner y a b = 0)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => (F.metric s).inner (Φ s x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ s) x w))
      ((1 / t) * (F.metric t).inner (Φ t x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w)) t := by
  apply (F.hasDerivAt_negativeGradient_pullback_metric hJ hf hs hΦ ht x v w).congr_deriv
  have h := hsol (Φ t x)
    (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w)
  have hcoef : (2 : ℝ) * (1 / (2 * t)) = 1 / t := by
    simp only [one_div, mul_inv_rev]
    ring
  rw [← hcoef]
  linear_combination -2 * h


theorem soliton_pullback_metric_eq_time_ratio
    (hzero : ∀ s ∈ J, s ≠ 0)
    (hsol : ∀ s ∈ J, ∀ y (a b : TangentSpace (𝓡 n) y),
      (F.connection s).ricci y a b + (F.connection s).hessian (fun z => f (s, z)) y a b +
        (1 / (2 * s)) * (F.metric s).inner y a b = 0)
    {s t : ℝ} (hsJ : s ∈ J) (htJ : t ∈ J) (x : M) (v w : TangentSpace (𝓡 n) x) :
    (F.metric t).inner (Φ t x)
      (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ t) x w) =
      (t / s) * (F.metric s).inner (Φ s x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ s) x w) := by
  let m : ℝ → ℝ := fun r => (F.metric r).inner (Φ r x)
    (mfderiv (𝓡 n) (𝓡 n) (Φ r) x v) (mfderiv (𝓡 n) (𝓡 n) (Φ r) x w)
  have hd (r : ℝ) (hr : r ∈ J) : HasDerivAt m ((1 / r) * m r) r :=
    F.hasDerivAt_soliton_pullback_metric hJ hf hs hΦ hr (hsol r hr) x v w
  have hz (r : ℝ) (hr : r ∈ J) : HasDerivAt (fun u => m u / u) 0 r := by
    apply ((hd r hr).div (hasDerivAt_id r) (hzero r hr)).congr_deriv
    dsimp only [id_eq]
    field_simp [hzero r hr]
    ring
  have heq : m t / t = m s / s := hJ.is_const_of_deriv_eq_zero F.interval.isPreconnected
    (fun r hr => (hz r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hz r hr).deriv) htJ hsJ
  change m t = (t / s) * m s
  calc
    m t = (m t / t) * t := (div_mul_cancel₀ (m t) (hzero t htJ)).symm
    _ = (m s / s) * t := by rw [heq]
    _ = (t / s) * m s := by ring

end PoincareConjecture.RicciFlow
