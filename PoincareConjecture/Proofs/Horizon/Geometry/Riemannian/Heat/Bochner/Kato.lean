import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import Mathlib.Analysis.SpecialFunctions.Sqrt










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in
private lemma contMDiff_sqrt_of_pos {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => Real.sqrt (f x)) := by
  intro x
  exact (Real.contDiffAt_sqrt (hpos x).ne').contMDiffAt.comp x (hf x)



theorem normalized_regularized_gradient_subsolution [T2Space M]
    (D : LeviCivitaData g) {F : ℝ × M → ℝ} {t k c : ℝ}
    (hF : ∀ x, ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x))
    (hheat : ∀ x, HasDerivAt (fun s => F (s, x))
      (D.laplacian (fun y => F (t, y)) x) t)
    (hk : 0 ≤ k) (x : M)
    (hRic : -k * g.inner x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x) ≤
      D.ricci x (D.gradient (fun y => F (t, y)) x)
        (D.gradient (fun y => F (t, y)) x)) :
    let q := fun s y => g.inner y (D.gradient (fun z => F (s, z)) y)
      (D.gradient (fun z => F (s, z)) y)
    deriv (fun s => Real.exp (-k * s) * Real.sqrt (q s x + 1) - c) t ≤
      D.laplacian (fun y => Real.exp (-k * t) * Real.sqrt (q t y + 1) - c) x := by
  let q := fun s y => g.inner y (D.gradient (fun z => F (s, z)) y)
    (D.gradient (fun z => F (s, z)) y)
  have hq0 (s : ℝ) (y : M) : 0 ≤ q s y := by
    by_cases h : D.gradient (fun z => F (s, z)) y = 0
    · simp [q, h]
    · exact (g.pos y _ h).le
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => F (t, y)) :=
    fun y => (hF y).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  have hq := D.contMDiff_inner_gradient hs hs
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => Real.sqrt (q t y + 1)) :=
    contMDiff_sqrt_of_pos (hq.add contMDiff_const) (fun y => by linarith [hq0 t y])
  have hqt := D.hasDerivAt_gradient_normSq_of_time_derivative (hF x) hheat
  have hwt := (hqt.add_const 1).sqrt (by linarith [hq0 t x] : q t x + 1 ≠ 0)
  have hzt := ((((hasDerivAt_id t).const_mul (-k)).exp).mul hwt).sub_const c
  simp only [Pi.mul_apply, id_eq, mul_one] at hzt
  have hlin : ContDiff ℝ ∞ (fun z : ℝ => Real.exp (-k * t) * z - c) :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have hlap := D.laplacian_comp hw hlin x
  simp [Function.comp_def] at hlap
  simp only [← neg_mul] at hlap
  have hb := D.heat_regularized_gradient_norm_subsolution hk
    (by norm_num : (0 : ℝ) < 1) hF hheat x hRic
  change deriv (fun s => Real.exp (-k * s) * Real.sqrt (q s x + 1) - c) t ≤ _
  have hderiv : deriv (fun s => Real.exp (-k * s) * Real.sqrt (q s x + 1) - c) t =
      Real.exp (-k * t) * (-k * Real.sqrt (q t x + 1)) +
        Real.exp (-k * t) * deriv (fun s => Real.sqrt (q s x + 1)) t := by
    rw [hzt.deriv, hwt.deriv]
    ring
  rw [hderiv]
  rw [hlap]
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-k * t))
  nlinarith

end PoincareConjecture.LeviCivitaData

namespace Poincare.Analysis.Heat



theorem regularized_norm_excess_sq_le {q θ c : ℝ} (hq : 0 ≤ q)
    (hθ1 : θ ≤ 1) (hc : 1 ≤ c) :
    max (θ * Real.sqrt (q + 1) - c) 0 ^ 2 ≤ q := by
  have hq1 : 0 ≤ q + 1 := by linarith
  have hs : Real.sqrt (q + 1) ≤ Real.sqrt q + 1 := by
    have h1 := Real.sq_sqrt hq1
    have h2 := Real.sq_sqrt hq
    nlinarith [Real.sqrt_nonneg q, Real.sqrt_nonneg (q + 1)]
  have hθ := mul_le_mul_of_nonneg_right hθ1 (Real.sqrt_nonneg (q + 1))
  have he : max (θ * Real.sqrt (q + 1) - c) 0 ≤ Real.sqrt q := by
    apply max_le
    · nlinarith
    · exact Real.sqrt_nonneg q
  have hnonneg : 0 ≤ max (θ * Real.sqrt (q + 1) - c) 0 := le_max_right _ _
  nlinarith [Real.sq_sqrt hq]

end Poincare.Analysis.Heat
