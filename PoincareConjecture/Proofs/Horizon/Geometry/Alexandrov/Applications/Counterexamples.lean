import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.PointedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Counterexamples











noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

theorem exists_rescaled_alexandrov_counterexample_limit_of_not_uniform_bound
    {n : ℕ}
    (hfail : ¬ ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M, (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C)
    (hn : 2 ≤ n) (c : ℕ → ℝ) (hc : ∀ j, 1 ≤ c j) :
    ∃ A : ℕ → PointedScalarModel n,
      (∀ j : ℕ, (j : ℝ) < (A j).unitBallScalarIntegral) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ q : ∀ j, (A (phi j)).carrier,
        (∀ j, q j ∈ (A (phi j)).metric.ball (A (phi j)).point 1) ∧
        let G := fun j => rescaledMetric (A (phi j)).metric (c j)
          (zero_lt_one.trans_le (hc j))
        let DS := fun j => rescaledMetric_connection (A (phi j)).metric
          (A (phi j)).connection (c j) (zero_lt_one.trans_le (hc j))
        ∃ theta : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
          StrictMono theta ∧ ProperSpace S.completedLimit.carrier ∧
          (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
            γ 0 = x ∧ γ 1 = y ∧
            ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
              dist (γ s) (γ t) = |s - t| * dist x y) ∧
          PointedGHConvergesUnbounded
            (fun j => (G (theta j)).toBasedMetricSpace (q (theta j))) S.completedLimit ∧
          Poincare.Alexandrov.CurvatureGEnegOne S.completedLimit.carrier ∧
          Tendsto (fun j => ∫ x in (G (theta j)).ball (q (theta j)) 1,
            (DS (theta j)).scalarCurvature x ∂(G (theta j)).volumeMeasure)
            atTop atTop := by
  obtain ⟨A, hA, phi, hphi, q, hq, theta, S, htheta, hproper, hgeo, hlim, hdiv⟩ :=
    exists_rescaled_counterexample_limit_of_not_uniform_bound hfail hn c hc
  refine ⟨A, hA, phi, hphi, q, hq, theta, S, htheta, hproper, hgeo, hlim, ?_, hdiv⟩
  let G := fun j => rescaledMetric (A (phi j)).metric (c j)
    (zero_lt_one.trans_le (hc j))
  let DS := fun j => rescaledMetric_connection (A (phi j)).metric
    (A (phi j)).connection (c j) (zero_lt_one.trans_le (hc j))
  have hcomplete (j : ℕ) : MetricComplete (G j) :=
    metricComplete_rescaledMetric (A (phi j)).metric (c j)
      (zero_lt_one.trans_le (hc j)) (A (phi j)).complete
  have hsec (j : ℕ) (x : (A (phi j)).carrier) (v w : TangentSpace (𝓡 n) x) :
      -1 ≤ (DS j).sectionalCurvature x v w := by
    have hfrac : (1 : ℝ) / c j ≤ 1 :=
      (div_le_one (zero_lt_one.trans_le (hc j))).2 (hc j)
    exact (neg_le_neg hfrac).trans
      (rescaledMetric_sectionalCurvature_lower_bound (A (phi j)).metric
        (A (phi j)).connection (c j) (zero_lt_one.trans_le (hc j))
        1 (A (phi j)).sectional_lower x v w)
  exact RiemannianMetric.curvatureGEnegOne_of_sectional_pointed_limit
    (fun j => G (theta j)) (fun j => q (theta j)) (fun j => DS (theta j))
    (fun j => hcomplete (theta j)) (fun j => hsec (theta j)) hlim

end PoincareConjecture
