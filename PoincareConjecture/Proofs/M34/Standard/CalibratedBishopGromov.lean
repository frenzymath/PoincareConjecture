import PoincareConjecture.Proofs.M34.Lemma12_3_CoreVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Precompact
import PoincareConjecture.Proofs.M09.RiemannianProper
import PoincareConjecture.Definitions.Ch09.AsymptoticVolume











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M34

open RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [SecondCountableTopology M]



theorem calibrated_ball_volume_ratio_antitoneOn_of_precompact
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v) :
    AntitoneOn (fun r : ℝ => calibratedMetricVolume g (g.ball p r) /
      ENNReal.ofReal r ^ n) (Ioo 0 R) := by
  rw [calibratedVolume_eq_volumeMeasure]
  have hc0 : ENNReal.ofReal (euclideanUnitBallVolume n) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (euclideanUnitBallVolume_pos n)).ne'
  have hnorm (r : ℝ) (hr : 0 < r) :
      (g.volumeMeasure (g.ball p r) / ENNReal.ofReal (modelVolume n 0 r)) *
          ENNReal.ofReal (euclideanUnitBallVolume n) =
        g.volumeMeasure (g.ball p r) / ENNReal.ofReal r ^ n := by
    rw [modelVolume_zero_curvature hn, ENNReal.ofReal_mul (euclideanUnitBallVolume_nonneg n),
      ENNReal.ofReal_pow hr.le,
      ENNReal.div_mul _ (Or.inr hc0) (Or.inr ENNReal.ofReal_ne_top),
      mul_comm (ENNReal.ofReal (euclideanUnitBallVolume n)),
      ENNReal.mul_div_cancel_right hc0 ENNReal.ofReal_ne_top]
  have hmono := (g.relativeVolumeComparison_of_precompact_ball p hn hR
    (le_refl (0 : ℝ)) hcompact D (by
      intro x hx v
      simpa only [mul_zero, neg_zero, zero_mul] using hRic x hx v)).1
  intro r hr s hs hrs
  have hmul := mul_le_mul' (hmono hr hs hrs)
    (le_refl (ENNReal.ofReal (euclideanUnitBallVolume n)))
  simpa only [hnorm r hr.1, hnorm s hs.1] using hmul



theorem antitoneMetricBallVolumeRatio_of_complete_nonnegative_ricci
    [ConnectedSpace M] (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hn : 1 ≤ n) (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v) (p : M) :
    AntitoneMetricBallVolumeRatio g p := by
  intro r s hrs
  have hs : 0 < (s : ℝ) := s.2
  have hmono := calibrated_ball_volume_ratio_antitoneOn_of_precompact g D p hn
    (mul_pos two_pos hs) (Proofs.M09.isCompact_closure_metric_ball g hcomplete p (2 * s))
    (fun x _ v => hRic x v)
  exact hmono ⟨r.2, by change (r : ℝ) ≤ s at hrs; linarith⟩
    ⟨s.2, by linarith⟩ hrs

end PoincareConjecture.M34
