import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Precompact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.ModelBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Moment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

lemma volumeMeasure_ball_growth_of_ricci
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PreconnectedSpace M] (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hn : 1 ≤ n) (hcomplete : MetricComplete g) {κ : ℝ} (hκ : 0 ≤ κ)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v)
    (p : M) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    g.volumeMeasure.real (g.ball p R) ≤ (R / r) ^ n *
      Real.exp ((n - 1 : ℕ) * (Real.sqrt κ * R)) * g.volumeMeasure.real (g.ball p r) := by
  let : SecondCountableTopology M := g.secondCountableTopology
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hR : 0 < R := hr.trans_le hrR
  have hclosed : IsClosed {q | g.edist p q ≤ ENNReal.ofReal (R + 1)} :=
    isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hcompact : IsCompact (closure (g.ball p (R + 1))) :=
    (g.isCompact_closedBall_of_metricComplete hcomplete p (R + 1)).of_isClosed_subset
      isClosed_closure (closure_minimal (fun q hq =>
        (show g.edist p q < ENNReal.ofReal (R + 1) from hq).le) hclosed)
  have hmono := (g.relativeVolumeComparison_of_precompact_ball p hn
    (show 0 < R + 1 by linarith) hκ hcompact D (fun x _ v => hRic x v)).1
      (show r ∈ Ioo 0 (R + 1) from ⟨hr, by linarith⟩)
      (show R ∈ Ioo 0 (R + 1) from ⟨hR, by linarith⟩) hrR
  have hvr := modelVolume_pos hn hκ hr
  have hvR := modelVolume_pos hn hκ hR
  have hreal := ENNReal.toReal_mono
    (ENNReal.div_ne_top (g.volumeMeasure_ball_lt_top hcomplete p r).ne
      (ENNReal.ofReal_pos.mpr hvr).ne') hmono
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofReal hvr.le,
    ENNReal.toReal_ofReal hvR.le] at hreal
  have hratio : g.volumeMeasure.real (g.ball p R) ≤
      (modelVolume n κ R / modelVolume n κ r) * g.volumeMeasure.real (g.ball p r) := by
    have h := (div_le_div_iff₀ hvR hvr).mp hreal
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hvr).mpr (by simpa only [Measure.real, mul_comm] using h)
  exact hratio.trans (mul_le_mul_of_nonneg_right (modelVolume_div_le hn hκ hr hR.le)
    ENNReal.toReal_nonneg)

theorem exists_first_moment_bound_of_ricci_gaussian
    (n : ℕ) (κ A c : ℝ) (hn : 0 < n) (hκ : 0 ≤ κ) (hA : 1 ≤ A) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [PreconnectedSpace M] (g : RiemannianMetric n M), MetricComplete g →
        ∀ D : LeviCivitaData g,
          (∀ x (v : TangentSpace (𝓡 n) x),
            -(((n : ℝ) - 1) * κ) * g.inner x v v ≤ D.ricci x v v) →
          ∀ H : M → M → ℝ → ℝ,
            (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x : M,
              Measurable (fun y => H x y t) ∧ (∀ y, 0 ≤ H x y t) ∧
                (∀ y, H x y t ≤ A / g.volumeMeasure.real (g.ball x (Real.sqrt t)) *
                  Real.exp (-(g.edist x y).toReal ^ 2 / (c * t)))) →
            (∀ x t, 0 < t → t ≤ 1 →
              Integrable (fun y => (g.edist x y).toReal * H x y t) g.volumeMeasure ∧
              (∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure) ≤ C) ∧
            Tendsto (fun t => ⨆ x, ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure)
              (𝓝[>] 0) (𝓝 0) := by
  let B : ℝ := (n - 1 : ℕ) * Real.sqrt κ
  obtain ⟨C, hC, hbound⟩ := exists_first_moment_bound_of_gaussian.{u} n A B c hn hA
    (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg κ)) hc
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ g hcomplete D hRic H hH
  have hgrowth (x : M) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
      g.volumeMeasure.real (g.ball x R) ≤ A * (R / r) ^ n * Real.exp (B * R) *
        g.volumeMeasure.real (g.ball x r) := by
    have h := g.volumeMeasure_ball_growth_of_ricci D hn hcomplete hκ hRic x hr hrR
    have h0 : 0 ≤ (R / r) ^ n * Real.exp (B * R) * g.volumeMeasure.real (g.ball x r) :=
      mul_nonneg (mul_nonneg (pow_nonneg (div_nonneg (hr.le.trans hrR) hr.le) _)
        (Real.exp_pos _).le) ENNReal.toReal_nonneg
    calc
      _ ≤ (R / r) ^ n * Real.exp (B * R) * g.volumeMeasure.real (g.ball x r) := by
        simpa only [B, mul_assoc] using h
      _ ≤ A * ((R / r) ^ n * Real.exp (B * R) * g.volumeMeasure.real (g.ball x r)) :=
        le_mul_of_one_le_left h0 hA
      _ = _ := by ring
  obtain ⟨hi, hb, _, hlim⟩ := hbound M g hcomplete hgrowth H hH
  exact ⟨fun x t ht ht1 => ⟨(hi x t ht ht1).1, hb x t ht ht1⟩, hlim⟩

end PoincareConjecture.RiemannianMetric
