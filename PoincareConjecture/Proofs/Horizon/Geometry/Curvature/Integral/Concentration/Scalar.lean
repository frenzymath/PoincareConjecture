import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.BallCover
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}



theorem integral_scalarCurvature_posPart_ball_le_integral_add_model
    (D : LeviCivitaData g) (p : M) (hn : 1 ≤ n)
    (hcomplete : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in g.ball p r, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      (∫ x in g.ball p r, D.scalarCurvature x ∂g.volumeMeasure) +
        (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 r := by
  have hiR := g.integrableOn_ball_of_continuous hcomplete D.continuous_scalarCurvature p r
  have hiP := g.integrableOn_ball_of_continuous hcomplete
    ((continuous_const (y := (0 : ℝ))).sup D.continuous_scalarCurvature) p r
  have hiC := g.integrableOn_ball_of_continuous hcomplete
    (continuous_const (y := (n : ℝ) ^ 2)) p r
  have hs : ∀ x : M, max 0 (D.scalarCurvature x) ≤ D.scalarCurvature x + (n : ℝ) ^ 2 := by
    intro x
    apply max_le
    · have hb := D.scalarCurvature_lower_bound_of_sectionalCurvature_lower_bound x 1 (hsec x)
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    · exact le_add_of_nonneg_right (sq_nonneg _)
  have hb := integral_mono hiP (hiR.add hiC) hs
  dsimp only [Pi.add_apply] at hb
  rw [integral_add hiR hiC, integral_const] at hb
  simp only [smul_eq_mul, measureReal_restrict_apply_univ] at hb
  have hv := g.volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
    p hn hcomplete D hsec hr
  nlinarith only [hb, mul_le_mul_of_nonneg_left hv (sq_nonneg (n : ℝ))]



theorem exists_smallBall_scalar_integral_gt
    (D : LeviCivitaData g) (p : M) (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hcomplete : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (C : ℝ)
    (hlarge : (⌈RiemannianMetric.modelVolume n 1 3 /
        RiemannianMetric.modelVolume n 1 (r / 2)⌉₊ : ℝ) *
        (C + (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 r) <
      ∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) :
    ∃ q ∈ g.ball p 1,
      C < ∫ x in g.ball q r, D.scalarCurvature x ∂g.volumeMeasure := by
  have hR : Continuous D.scalarCurvature := D.continuous_scalarCurvature
  have hRn (x : M) : 0 ≤ D.scalarCurvature x + (n : ℝ) ^ 2 := by
    have h := D.scalarCurvature_lower_bound_of_sectionalCurvature_lower_bound x 1 (hsec x)
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hi (q : M) (s : ℝ) := g.integrableOn_ball_of_continuous hcomplete hR q s
  have hci (q : M) (s : ℝ) := g.integrableOn_ball_of_continuous hcomplete
    (continuous_const (y := (n : ℝ) ^ 2)) q s
  have hshift (q : M) (s : ℝ) :
      (∫ x in g.ball q s, D.scalarCurvature x + (n : ℝ) ^ 2 ∂g.volumeMeasure) =
        (∫ x in g.ball q s, D.scalarCurvature x ∂g.volumeMeasure) +
          (n : ℝ) ^ 2 * g.volumeMeasure.real (g.ball q s) := by
    rw [integral_add (hi q s) (hci q s), integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    rw [mul_comm]
  obtain ⟨q, hq, hconcentration⟩ := g.exists_unitBall_integral_concentration p hn hr hr1
    hcomplete D hsec (hR.add continuous_const) hRn
  dsimp only [Pi.add_apply] at hconcentration
  rw [hshift p 1, hshift q r] at hconcentration
  refine ⟨q, hq, ?_⟩
  let N : ℝ := ⌈RiemannianMetric.modelVolume n 1 3 /
    RiemannianMetric.modelVolume n 1 (r / 2)⌉₊
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hunit : 0 ≤ (n : ℝ) ^ 2 * g.volumeMeasure.real (g.ball p 1) :=
    mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
  have hvol := g.volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
    q hn hcomplete D hsec hr
  have hupper :
      (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤
        N * ((∫ x in g.ball q r, D.scalarCurvature x ∂g.volumeMeasure) +
          (n : ℝ) ^ 2 * RiemannianMetric.modelVolume n 1 r) := by
    calc
      _ ≤ (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) +
          (n : ℝ) ^ 2 * g.volumeMeasure.real (g.ball p 1) := le_add_of_nonneg_right hunit
      _ ≤ N * ((∫ x in g.ball q r, D.scalarCurvature x ∂g.volumeMeasure) +
          (n : ℝ) ^ 2 * g.volumeMeasure.real (g.ball q r)) := hconcentration
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvol (sq_nonneg _))) hN
  by_contra hsmall
  have hupper' := hupper.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_of_not_gt hsmall) le_rfl) hN)
  exact (not_lt_of_ge hupper') hlarge

end PoincareConjecture.LeviCivitaData
