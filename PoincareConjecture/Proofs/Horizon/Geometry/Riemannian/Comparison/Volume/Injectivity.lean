import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.ExponentialLower
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Exponential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem unit_ball_volume_lower_bound_of_le_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (p : M) {K C r : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hr1 : r ≤ 1)
    (hrK : r ≤ Poincare.ODE.Jacobi.comparisonRadius K)
    (hrρ : r ≤ g.truncatedInjectivityRadius hc C p)
    (hcurv : ∀ x : M, D.curvatureTensorNorm x ≤ K) :
    ENNReal.ofReal (((n.factorial : ℝ) * (2 : ℝ) ^ n)⁻¹) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤
      g.volumeMeasure (g.ball p 1) := by
  have hcompact := g.isCompact_closedBall_of_metricComplete hc p 1
  have hclosure : IsCompact (closure (g.ball p 1)) :=
    hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => show g.edist p x ≤ ENNReal.ofReal 1 from hx.le)
        hcompact.isClosed)
  obtain ⟨L, e, hL, he, he0, hed, hgeo, hb⟩ :=
    g.exists_precompact_exponential_with_differential_bounds D p
      (by norm_num : (0 : ℝ) < 1) hK hclosure (fun x _ => hcurv x)
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball hr1
  apply g.ball_volume_lower_bound_of_injective_exponential p (he.mono hsub)
    (g.injOn_radial_exponential_of_le_truncatedInjectivityRadius hc p
      (by norm_num : (0 : ℝ) < 1) hC hr1 hrρ L e hL he0 hed
      (fun v hv => (hgeo v hv).1))
  · intro v hv
    have hdist := ((hgeo v (hsub hv)).2 1 (by norm_num)).2
    simp only [one_smul, ENNReal.ofReal_one, mul_one] at hdist
    exact hdist.trans_lt (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1) |>.mpr
      ((show ‖v‖ < r by simpa using hv).trans_le hr1))
  · intro v hv w
    exact (hb v (hsub hv) ((show ‖v‖ < r by simpa using hv).le.trans hrK)).2 w |>.1



theorem exists_uniform_unit_ball_volume_lower_bound_of_injectivity
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {K C ρ : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hsec : ∀ x (u v : TangentSpace (𝓡 n) x), |D.sectionalCurvature x u v| ≤ K)
    (hinj : ∀ x : M, ρ ≤ g.truncatedInjectivityRadius hc C x) :
    ∃ v : ℝ, 0 < v ∧ ∀ x : M,
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball x 1) := by
  let K' := 4 * (n : ℝ) ^ 2 * K
  have hK' : 0 ≤ K' := by dsimp [K']; positivity
  let r := min 1 (min ρ (Poincare.ODE.Jacobi.comparisonRadius K'))
  have hr : 0 < r := lt_min zero_lt_one
    (lt_min hρ (Poincare.ODE.Jacobi.comparisonRadius_pos K'))
  let v : ℝ≥0∞ := ENNReal.ofReal (((n.factorial : ℝ) * (2 : ℝ) ^ n)⁻¹) *
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
  have hvpos : 0 < v := by
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      (Metric.measure_ball_pos volume _ hr).ne'
  have hvfinite : v ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  refine ⟨v.toReal, ENNReal.toReal_pos hvpos.ne' hvfinite, ?_⟩
  intro p
  rw [ENNReal.ofReal_toReal hvfinite]
  exact g.unit_ball_volume_lower_bound_of_le_truncatedInjectivityRadius D hc p
    hK' hC (min_le_left _ _)
    ((min_le_right _ _).trans (min_le_right _ _))
    (((min_le_right _ _).trans (min_le_left _ _)).trans (hinj p))
    (fun x => D.curvatureTensorNorm_le_of_sectional x hK (hsec x))

end PoincareConjecture.RiemannianMetric
