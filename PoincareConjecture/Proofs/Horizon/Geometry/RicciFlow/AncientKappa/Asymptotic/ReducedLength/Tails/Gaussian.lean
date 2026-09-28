import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.VolumeBounds
import PoincareConjecture.Proofs.Horizon.Analysis.Measure.GaussianTails.PolynomialVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientRescalingSequence

open Poincare.Analysis RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem exp_neg_reducedLength_gaussian_tail
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) {τ R : ℝ} (hτ : 0 < τ) (hR : 0 ≤ R) :
    ∫⁻ q in (((S.rescaling k).flow.metric (-τ)).ball (S.base k) R)ᶜ,
      ENNReal.ofReal (Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ)))
        ∂calibratedMetricVolume ((S.rescaling k).flow.metric (-τ)) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹ + 1) *
        (Real.exp (-(16 * (2 * (n : ℝ) + 604) ^ 2 * τ)⁻¹ / 2 * R ^ 2) *
          (euclideanUnitBallVolume n *
            gaussianShellSum n ((16 * (2 * (n : ℝ) + 604) ^ 2 * τ)⁻¹ / 2)))) := by
  let g := (S.rescaling k).flow.metric (-τ)
  let := g.toMetricSpace
  let d : M → ℝ := fun q => (g.edist (S.base k) q).toReal
  let a := (16 * (2 * (n : ℝ) + 604) ^ 2 * τ)⁻¹
  let A := Real.exp ((n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹ + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : Measurable d := (continuous_const.dist continuous_id).measurable
  have hd0 (q : M) : 0 ≤ d q := ENNReal.toReal_nonneg
  have hvol (m : ℕ) : calibratedMetricVolume g {q | d q < (m : ℝ) + 1} ≤
      ENNReal.ofReal (euclideanUnitBallVolume n * ((m : ℝ) + 1) ^ n) := by
    have heq : {q | d q < (m : ℝ) + 1} = g.ball (S.base k) ((m : ℝ) + 1) := by
      ext q
      exact (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top (S.base k) q)).symm
    rw [heq]
    exact S.rescaled_ball_volume_le_euclidean P k hτ (S.base k) (by positivity)
  have hcomp : (g.ball (S.base k) R)ᶜ = {q | R ≤ d q} := by
    ext q
    change ¬ g.edist (S.base k) q < ENNReal.ofReal R ↔ R ≤ d q
    rw [ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top (S.base k) q), not_lt]
  have htail := lintegral_gaussian_tail_le_of_sublevel_volume hd hd0 ha
    (euclideanUnitBallVolume_nonneg n) hR hvol
  change (∫⁻ q in (g.ball (S.base k) R)ᶜ,
    ENNReal.ofReal (Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ)))
      ∂calibratedMetricVolume g) ≤ _
  rw [hcomp]
  calc
    (∫⁻ q in {q | R ≤ d q},
        ENNReal.ofReal (Real.exp (-reducedLength K.flow 0 S.reference q (S.scale k * τ)))
          ∂calibratedMetricVolume g) ≤
        ∫⁻ q in {q | R ≤ d q}, ENNReal.ofReal A *
          ENNReal.ofReal (Real.exp (-a * (d q) ^ 2)) ∂calibratedMetricVolume g := by
      apply lintegral_mono
      intro q
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      convert! S.exp_neg_reducedLength_le_gaussian P k hτ q using 1
      dsimp [A, a, d, g]
      congr 2
      ring
    _ = ENNReal.ofReal A * (∫⁻ q in {q | R ≤ d q},
        ENNReal.ofReal (Real.exp (-a * (d q) ^ 2)) ∂calibratedMetricVolume g) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal
        (Real.exp (-a / 2 * R ^ 2) * (euclideanUnitBallVolume n * gaussianShellSum n (a / 2))) := by
      gcongr
    _ = _ := (ENNReal.ofReal_mul (Real.exp_nonneg _)).symm

end PoincareConjecture.AncientRescalingSequence
