import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.LimitPacking
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.AreaSlabs














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

theorem exists_rescaled_counterexample_with_area_controlled_regular_slabs_of_not_uniform_bound
    {n : ℕ}
    (hfail : ¬ ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
        [IsManifold (𝓡 (n + 1)) ∞ M]
        (g : RiemannianMetric (n + 1) M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ x (v w : TangentSpace (𝓡 (n + 1)) x), -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M, (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C)
    (hn : 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ j, 1 ≤ c j) :
    ∃ A : ℕ → PointedScalarModel (n + 1),
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
          (∀ α : ℝ, 0 < α → ∃ N : ℕ,
            Poincare.Alexandrov.ComparisonAnglePackingBound S.completedLimit.carrier α N) ∧
          (∀ v : ℝ, 0 ≤ v → v < 1 → ∀ p : S.completedLimit.carrier,
            ∃ r : ℝ, 0 < r ∧ ∀ y : S.completedLimit.carrier,
              0 < dist p y → dist p y < r → ∀ s : ℝ, 0 < s →
                ∃ z : S.completedLimit.carrier, dist y z < s ∧
                  v * dist y z < dist p z - dist p y) ∧
          Tendsto (fun j => ∫ x in (G (theta j)).ball (q (theta j)) 1,
            (DS (theta j)).scalarCurvature x ∂(G (theta j)).volumeMeasure)
            atTop atTop ∧
          ∃ r ε H α : ℝ, 0 < r ∧ 0 < ε ∧ ε < r / 128 ∧ 0 < H ∧ 0 < α ∧
            ∀ᶠ j in atTop, ∃ (f : (A (phi (theta j))).carrier → ℝ)
              (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f),
              IsProperMap ((Ioo (9 * r / 8) (15 * r / 8)).restrictPreimage f) ∧
              (∀ x : (A (phi (theta j))).carrier, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
                mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
              (∀ x : (A (phi (theta j))).carrier, f x ∈ Ioo (9 * r / 8) (15 * r / 8) →
                r < ((G (theta j)).edist (q (theta j)) x).toReal ∧
                  ((G (theta j)).edist (q (theta j)) x).toReal < 2 * r) ∧
              (∀ x : (A (phi (theta j))).carrier,
                r < ((G (theta j)).edist (q (theta j)) x).toReal →
                ((G (theta j)).edist (q (theta j)) x).toReal < 2 * r →
                |f x - ((G (theta j)).edist (q (theta j)) x).toReal| ≤ ε ∧
                (1 : ℝ) / 4 ≤ (G (theta j)).tangentNorm x ((DS (theta j)).gradient f x) ∧
                (G (theta j)).tangentNorm x ((DS (theta j)).gradient f x) ≤ 2 ∧
                ∀ v : TangentSpace (𝓡 (n + 1)) x,
                  (DS (theta j)).hessian f x v v ≤ H * (G (theta j)).inner x v v) ∧
              ∀ t ∈ Icc (7 * r / 6) (11 * r / 6),
                (G (theta j)).regularLevelArea hf t ≤ α * t ^ n := by
  obtain ⟨A, hA, phi, hphi, q, hq, theta, S, htheta, hproper, hgeo, hlim,
    hcurv, hpacking, hascent, hdiv⟩ :=
    exists_rescaled_counterexample_limit_with_angle_packing_of_not_uniform_bound
      hfail (by omega) c hc
  let G := fun j => rescaledMetric (A (phi j)).metric (c j)
    (zero_lt_one.trans_le (hc j))
  let DS := fun j => rescaledMetric_connection (A (phi j)).metric
    (A (phi j)).connection (c j) (zero_lt_one.trans_le (hc j))
  have hcomplete (j : ℕ) : MetricComplete (G j) :=
    metricComplete_rescaledMetric (A (phi j)).metric (c j)
      (zero_lt_one.trans_le (hc j)) (A (phi j)).complete
  have hsec (j : ℕ) (x : (A (phi j)).carrier) (v w : TangentSpace (𝓡 (n + 1)) x) :
      -1 ≤ (DS j).sectionalCurvature x v w := by
    have hfrac : (1 : ℝ) / c j ≤ 1 :=
      (div_le_one (zero_lt_one.trans_le (hc j))).2 (hc j)
    exact (neg_le_neg hfrac).trans
      (rescaledMetric_sectionalCurvature_lower_bound (A (phi j)).metric
        (A (phi j)).connection (c j) (zero_lt_one.trans_le (hc j))
        1 (A (phi j)).sectional_lower x v w)
  let : ProperSpace S.completedLimit.carrier := hproper
  refine ⟨A, hA, phi, hphi, q, hq, theta, S, htheta, hproper, hgeo, hlim,
    hcurv, hpacking, hascent, hdiv, ?_⟩
  exact RiemannianMetric.exists_eventually_area_controlled_regular_slabs_of_sectional_pointed_limit
    (fun j => G (theta j)) (fun j => DS (theta j))
    (fun j => hcomplete (theta j)) (fun j => hsec (theta j))
    (fun j => q (theta j)) hgeo hlim

end PoincareConjecture
