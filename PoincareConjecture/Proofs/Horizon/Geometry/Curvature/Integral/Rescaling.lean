import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Measure
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Volume









noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

section ScalarIntegrals

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem rescaledMetric_integral_scalarCurvature
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (s : Set M) :
    (∫ x in s, (rescaledMetric_connection g D c hc).scalarCurvature x
      ∂(rescaledMetric g c hc).volumeMeasure) =
      (Real.sqrt c) ^ n / c * ∫ x in s, D.scalarCurvature x ∂g.volumeMeasure := by
  simp only [rescaledMetric_volumeMeasure, Measure.restrict_smul,
    integral_smul_measure, rescaledMetric_scalarCurvature, integral_const_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg c), smul_eq_mul]
  rw [div_eq_mul_inv]
  ring


theorem rescaledMetric_integral_scalarCurvature_ball
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) :
    (∫ x in (rescaledMetric g c hc).ball p r,
      (rescaledMetric_connection g D c hc).scalarCurvature x
        ∂(rescaledMetric g c hc).volumeMeasure) =
      (Real.sqrt c) ^ n / c *
        ∫ x in g.ball p (r / Real.sqrt c), D.scalarCurvature x ∂g.volumeMeasure := by
  rw [rescaledMetric_integral_scalarCurvature, rescaledMetric_ball]


theorem rescaledMetric_integral_scalarCurvature_unitBall
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (p : M) :
    (∫ x in (rescaledMetric g c hc).ball p 1,
      (rescaledMetric_connection g D c hc).scalarCurvature x
        ∂(rescaledMetric g c hc).volumeMeasure) =
      (Real.sqrt c) ^ n / c *
        ∫ x in g.ball p (Real.sqrt c)⁻¹, D.scalarCurvature x ∂g.volumeMeasure := by
  simpa only [one_div] using rescaledMetric_integral_scalarCurvature_ball g D c hc p 1


theorem rescaledMetric_integral_scalarCurvature_ball_mul
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) :
    (∫ x in (rescaledMetric g c hc).ball p (Real.sqrt c * r),
      (rescaledMetric_connection g D c hc).scalarCurvature x
        ∂(rescaledMetric g c hc).volumeMeasure) =
      (Real.sqrt c) ^ (n - 2) *
        ∫ x in g.ball p r, D.scalarCurvature x ∂g.volumeMeasure := by
  rw [rescaledMetric_integral_scalarCurvature_ball,
    mul_div_cancel_left₀ r (Real.sqrt_pos.mpr hc).ne']
  congr 1
  rw [pow_sub₀ (Real.sqrt c) (Real.sqrt_pos.mpr hc).ne' hn, Real.sq_sqrt hc.le,
    div_eq_mul_inv]

end ScalarIntegrals




theorem exists_subseq_proper_geodesic_pointed_limit_of_metric_rescaling
    {n : ℕ} {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j)) (p : ∀ j, M j)
    (hn : 1 ≤ n) (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (c : ℕ → ℝ) (hc : ∀ j, 1 ≤ c j) :
    let G := fun j => PoincareConjecture.rescaledMetric (g j) (c j) (zero_lt_one.trans_le (hc j))
    ∃ phi : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
      StrictMono phi ∧ ProperSpace S.completedLimit.carrier ∧
      (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
        γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y) ∧
      PointedGHConvergesUnbounded
        (fun j => (G (phi j)).toBasedMetricSpace (p (phi j))) S.completedLimit := by
  let G := fun j => rescaledMetric (g j) (c j) (zero_lt_one.trans_le (hc j))
  let DS := fun j => rescaledMetric_connection (g j) (D j) (c j)
    (zero_lt_one.trans_le (hc j))
  have hcomplete' (j : ℕ) : MetricComplete (G j) :=
    metricComplete_rescaledMetric (g j) (c j) (zero_lt_one.trans_le (hc j)) (hcomplete j)
  have hsec' (j : ℕ) (x : M j) (v w : TangentSpace (𝓡 n) x) :
      -1 ≤ (DS j).sectionalCurvature x v w := by
    have hfrac : (1 : ℝ) / c j ≤ 1 :=
      (div_le_one (zero_lt_one.trans_le (hc j))).2 (hc j)
    exact (neg_le_neg hfrac).trans
      (rescaledMetric_sectionalCurvature_lower_bound (g j) (D j) (c j)
        (zero_lt_one.trans_le (hc j)) 1 (hsec j) x v w)
  exact RiemannianMetric.exists_subseq_proper_geodesic_pointed_limit_of_ricci_lower_bound
    G p hn 1 (by norm_num) hcomplete' DS (fun j x v =>
      (DS j).ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound x 1 (hsec' j x) v)




theorem exists_subseq_rescaled_pointed_limit_scalar_integral_tendsto_atTop
    {n : ℕ} {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j)) (p : ∀ j, M j)
    (hn : 2 ≤ n) (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (hlarge : ∀ C : ℝ, ∃ j : ℕ,
      C < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    (c : ℕ → ℝ) (hc : ∀ j, 1 ≤ c j) :
    let G := fun j => PoincareConjecture.rescaledMetric (g j) (c j) (zero_lt_one.trans_le (hc j))
    let DS := fun j => PoincareConjecture.rescaledMetric_connection (g j) (D j) (c j)
      (zero_lt_one.trans_le (hc j))
    ∃ phi : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
      StrictMono phi ∧ ProperSpace S.completedLimit.carrier ∧
      (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
        γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y) ∧
      PointedGHConvergesUnbounded
        (fun j => (G (phi j)).toBasedMetricSpace (p (phi j))) S.completedLimit ∧
      Tendsto
        (fun j => ∫ x in (G (phi j)).ball (p (phi j)) (Real.sqrt (c (phi j))),
          (DS (phi j)).scalarCurvature x ∂(G (phi j)).volumeMeasure)
        atTop atTop := by
  obtain ⟨psi, _, hpsi, _, _, _, hdiv⟩ :=
    exists_subseq_proper_geodesic_pointed_limit_scalar_integral_tendsto_atTop
      g p (by omega) hcomplete D hsec hlarge
  obtain ⟨theta, S, htheta, hproper, hgeodesic, hconverges⟩ :=
    exists_subseq_proper_geodesic_pointed_limit_of_metric_rescaling
      (fun j => g (psi j)) (fun j => p (psi j)) (by omega)
      (fun j => hcomplete (psi j)) (fun j => D (psi j)) (fun j => hsec (psi j))
      (fun j => c (psi j)) (fun j => hc (psi j))
  refine ⟨psi ∘ theta, S, hpsi.comp htheta, hproper, hgeodesic, hconverges, ?_⟩
  have hdiv' := hdiv.comp htheta.tendsto_atTop
  apply tendsto_atTop_mono' atTop ?_ hdiv'
  filter_upwards [hdiv'.eventually (eventually_ge_atTop 0)] with j hj
  dsimp only [Function.comp_def] at hj ⊢
  have heq := rescaledMetric_integral_scalarCurvature_ball_mul
    (g (psi (theta j))) (D (psi (theta j))) hn (c (psi (theta j)))
    (zero_lt_one.trans_le (hc (psi (theta j)))) (p (psi (theta j))) 1
  simp only [mul_one] at heq
  rw [heq]
  exact le_mul_of_one_le_left hj (one_le_pow₀ (Real.one_le_sqrt.mpr (hc _)))

end PoincareConjecture
