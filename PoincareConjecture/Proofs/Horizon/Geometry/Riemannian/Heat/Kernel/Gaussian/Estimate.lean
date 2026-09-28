import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Gaussian.Decay
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Gaussian.Harnack
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Gaussian.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.VolumeGrowth










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RiemannianMetric



theorem exists_gaussian_bound_of_double_ball_estimates
    (n : ℕ) (κ C : ℝ) (hn : 0 < n) (hκ : 0 ≤ κ) (hC : 0 ≤ C) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [PreconnectedSpace M] (g : RiemannianMetric n M), MetricComplete g →
        ∀ D : LeviCivitaData g,
          (∀ x (v : TangentSpace (𝓡 n) x),
            -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v) →
          ∀ H : ℝ → M → M → ℝ,
            (∀ t, 0 < t → Measurable (fun p : M × M => H t p.1 p.2)) →
            (∀ t, 0 < t → ∀ x y, 0 ≤ H t x y) →
            (∀ t, 0 < t → ∀ x y, H t x y = H t y x) →
            (∀ t, 0 < t → ∀ x, Integrable (H t x) g.volumeMeasure) →
            (∀ t, 0 < t → ∀ x, (∫ y, H t x y ∂g.volumeMeasure) ≤ 1) →
            (∀ a b, 0 < a → a < b → ∀ x z y,
              H a x y ≤ H b z y * Real.exp (2 * (n : ℝ) * Real.log (b / a) +
                C * (b - a) + (g.edist x z).toReal ^ 2 / (2 * (b - a)))) →
            (∀ t, 0 < t → ∀ x y,
              (∫ z in g.ball x (Real.sqrt t), ∫ w in g.ball y (Real.sqrt t),
                H (3 * t) z w ∂g.volumeMeasure ∂g.volumeMeasure) ≤
              Real.sqrt (g.volumeMeasure.real (g.ball x (Real.sqrt t))) *
                Real.sqrt (g.volumeMeasure.real (g.ball y (Real.sqrt t))) *
                  Real.exp (-(max ((g.edist x y).toReal - 2 * Real.sqrt t) 0) ^ 2 /
                    (48 * t))) →
            ∀ t, 0 < t → t ≤ 1 → ∀ x y,
              H t x y ≤ A / g.volumeMeasure.real (g.ball x (Real.sqrt t)) *
                Real.exp (-(g.edist x y).toReal ^ 2 / (192 * t)) := by
  let B : ℝ := (n - 1 : ℕ) * Real.sqrt κ
  let A0 := Real.exp (2 * (n : ℝ) * Real.log 3 + 2 * C + 13 / 12)
  obtain ⟨A, hA, hnorm⟩ := exists_gaussian_normalization_constant.{u} n 1 B 96 A0
    (by norm_num) (by dsimp [B]; positivity) (by norm_num) (Real.exp_pos _)
  refine ⟨max 1 A, le_max_left _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g hc D hRic H hmeas hnonneg hsymm hrow hmass hH hI t ht ht1 x y
  have hballs : ∀ p : M, ∀ r > 0, 0 < g.volumeMeasure (g.ball p r) ∧
      g.volumeMeasure (g.ball p r) < ⊤ :=
    fun p r hr => ⟨g.volumeMeasure_ball_pos p hr, g.volumeMeasure_ball_lt_top hc p r⟩
  have hgrowth : ∀ p : M, ∀ r R : ℝ, 0 < r → r ≤ R →
      g.volumeMeasure.real (g.ball p R) ≤ 1 * (R / r) ^ n * Real.exp (B * R) *
        g.volumeMeasure.real (g.ball p r) := by
    intro p r R hr hrR
    simpa only [one_mul, B, mul_assoc] using
      g.volumeMeasure_ball_growth_of_ricci D hn hc hκ hRic p hr hrR
  have hx := ENNReal.toReal_pos (hballs x _ (Real.sqrt_pos.mpr ht)).1.ne'
    (hballs x _ (Real.sqrt_pos.mpr ht)).2.ne
  have hy := ENNReal.toReal_pos (hballs y _ (Real.sqrt_pos.mpr ht)).1.ne'
    (hballs y _ (Real.sqrt_pos.mpr ht)).2.ne
  have havg := (LeviCivitaData.heatKernel_le_double_ball_integral_of_harnack hc
    hmeas hnonneg hsymm hrow hmass hH ht x y).2
  have hsymgauss := LeviCivitaData.gaussian_bound_of_double_ball_bounds n
    ENNReal.toReal_nonneg ht ht1 hx hy hC havg (hI t ht x y)
  have hnormgauss := hnorm M g hballs hgrowth t ht ht1 x y (H t x y) hsymgauss
  norm_num only [show (2 : ℝ) * 96 = 192 by norm_num] at hnormgauss
  exact hnormgauss.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (le_max_right 1 A) hx.le) (Real.exp_pos _).le)

end PoincareConjecture.RiemannianMetric
