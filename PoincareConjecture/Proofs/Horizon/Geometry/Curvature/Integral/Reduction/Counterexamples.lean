import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Blowup

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

structure PointedScalarModel (n : ℕ) where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [measurable : MeasurableSpace carrier]
  [borel : BorelSpace carrier]
  [separation : T3Space carrier]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) carrier]
  [smooth : IsManifold (𝓡 n) ∞ carrier]
  [connected : PreconnectedSpace carrier]
  metric : RiemannianMetric n carrier
  connection : LeviCivitaData metric
  point : carrier
  complete : MetricComplete metric
  sectional_lower : ∀ x (v w : TangentSpace (𝓡 n) x),
    -1 ≤ connection.sectionalCurvature x v w

attribute [instance] PointedScalarModel.topology PointedScalarModel.measurable
  PointedScalarModel.borel PointedScalarModel.separation PointedScalarModel.charts
  PointedScalarModel.smooth PointedScalarModel.connected

def PointedScalarModel.unitBallScalarIntegral {n : ℕ} (A : PointedScalarModel n) : ℝ :=
  ∫ x in A.metric.ball A.point 1, A.connection.scalarCurvature x ∂A.metric.volumeMeasure

section Counterexamples

variable {n : ℕ}
  (hfail : ¬ ∃ C : ℝ, 0 < C ∧
    ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g),
      MetricComplete g →
      (∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) →
      ∀ p : M, (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C)

include hfail

theorem exists_pointedScalarModel_above_of_not_uniform_bound (C : ℝ) :
    ∃ A : PointedScalarModel n, C < A.unitBallScalarIntegral := by
  classical
  by_contra hno
  have hbound (A : PointedScalarModel n) : A.unitBallScalarIntegral ≤ C :=
    le_of_not_gt (fun h => hno ⟨A, h⟩)
  apply hfail
  refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro M _ _ _ _ _ _ g D hcomplete hsec p
  apply (g.scalar_integral_le_of_small_connected_bound D hcomplete hsec C ?_ p).trans
    (le_max_left _ _)
  intro N _ _ _ _ _ _ _ gN DN hcompleteN hsecN q
  exact hbound
    { carrier := N
      metric := gN
      connection := DN
      point := q
      complete := hcompleteN
      sectional_lower := hsecN }

theorem exists_pointedScalarModels_of_not_uniform_bound :
    ∃ A : ℕ → PointedScalarModel n,
      (∀ j : ℕ, (j : ℝ) < (A j).unitBallScalarIntegral) ∧
      Tendsto (fun j => (A j).unitBallScalarIntegral) atTop atTop := by
  choose A hA using fun j : ℕ =>
    exists_pointedScalarModel_above_of_not_uniform_bound hfail (j : ℝ)
  exact ⟨A, hA, tendsto_atTop_mono (fun j => (hA j).le) tendsto_natCast_atTop_atTop⟩

theorem exists_rescaled_counterexample_limit_of_not_uniform_bound
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
          Tendsto (fun j => ∫ x in (G (theta j)).ball (q (theta j)) 1,
            (DS (theta j)).scalarCurvature x ∂(G (theta j)).volumeMeasure)
            atTop atTop := by
  obtain ⟨A, hA, _⟩ := exists_pointedScalarModels_of_not_uniform_bound hfail
  have hlarge : ∀ C : ℝ, ∃ j : ℕ, C < (A j).unitBallScalarIntegral := by
    intro C
    obtain ⟨j, hj⟩ := exists_nat_gt C
    exact ⟨j, hj.trans (hA j)⟩
  refine ⟨A, hA, ?_⟩
  exact exists_concentrated_rescaled_pointed_limit_scalar_integral_tendsto_atTop
    (fun j => (A j).metric) (fun j => (A j).point) hn (fun j => (A j).complete)
    (fun j => (A j).connection) (fun j => (A j).sectional_lower) hlarge c hc

end Counterexamples
end PoincareConjecture
