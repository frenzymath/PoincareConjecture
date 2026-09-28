import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.LimitPacking
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.LocalRank

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff Poincare.Alexandrov
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem exists_maximal_rank_scalar_counterexample_limit
    (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ,
      ∀ _hfail : ¬ ∃ C : ℝ, 0 < C ∧
        ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
          [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
          [IsManifold (𝓡 n) ∞ M]
          (g : RiemannianMetric n M) (D : LeviCivitaData g),
          MetricComplete g →
          (∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) →
          ∀ p : M, (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C,
      ∃ A : ℕ → PointedScalarModel n, ∃ S : CompatiblePointedCompactSystem.{0},
        ProperSpace S.completedLimit.carrier ∧
        (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
          γ 0 = x ∧ γ 1 = y ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist x y) ∧
        PointedGHConvergesUnbounded
          (fun j => (A j).metric.toBasedMetricSpace (A j).point) S.completedLimit ∧
        Tendsto (fun j => (A j).unitBallScalarIntegral) atTop atTop ∧
        CurvatureGEnegOne S.completedLimit.carrier ∧
        ComparisonAnglePackingBound S.completedLimit.carrier θ N ∧
        (∀ α : ℝ, 0 < α → ∃ L : ℕ,
          ComparisonAnglePackingBound S.completedLimit.carrier α L) ∧
        minLocalAnglePackingRank S.completedLimit.carrier θ ≤ N ∧
        ∀ (A' : ℕ → PointedScalarModel n) (S' : CompatiblePointedCompactSystem.{0}),
          ProperSpace S'.completedLimit.carrier →
          (∀ x y : S'.completedLimit.carrier, ∃ γ : ℝ → S'.completedLimit.carrier,
            γ 0 = x ∧ γ 1 = y ∧
            ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
              dist (γ s) (γ t) = |s - t| * dist x y) →
          PointedGHConvergesUnbounded
            (fun j => (A' j).metric.toBasedMetricSpace (A' j).point) S'.completedLimit →
          Tendsto (fun j => (A' j).unitBallScalarIntegral) atTop atTop →
          minLocalAnglePackingRank S'.completedLimit.carrier θ ≤
            minLocalAnglePackingRank S.completedLimit.carrier θ := by
  classical
  obtain ⟨N, hN⟩ :=
    RiemannianMetric.exists_comparisonAngle_packing_bound_of_sectional_pointed_limit.{0} n hθ
  refine ⟨N, ?_⟩
  intro hfail
  let ranks : Set ℕ := {k | ∃ A : ℕ → PointedScalarModel n,
    ∃ S : CompatiblePointedCompactSystem.{0},
      ProperSpace S.completedLimit.carrier ∧
      (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
        γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y) ∧
      PointedGHConvergesUnbounded
        (fun j => (A j).metric.toBasedMetricSpace (A j).point) S.completedLimit ∧
      Tendsto (fun j => (A j).unitBallScalarIntegral) atTop atTop ∧
      minLocalAnglePackingRank S.completedLimit.carrier θ = k}
  have hnonempty : ranks.Nonempty := by
    obtain ⟨A, hA, _⟩ := exists_pointedScalarModels_of_not_uniform_bound hfail
    have hlarge : ∀ C : ℝ, ∃ j, C < (A j).unitBallScalarIntegral := by
      intro C
      obtain ⟨j, hj⟩ := exists_nat_gt C
      exact ⟨j, hj.trans (hA j)⟩
    obtain ⟨φ, S, _, hproper, hgeo, hconv, hdiv⟩ :=
      exists_subseq_proper_geodesic_pointed_limit_scalar_integral_tendsto_atTop
        (fun j => (A j).metric) (fun j => (A j).point) (by omega)
        (fun j => (A j).complete) (fun j => (A j).connection)
        (fun j => (A j).sectional_lower) hlarge
    exact ⟨minLocalAnglePackingRank S.completedLimit.carrier θ,
      (fun j => A (φ j)), S, hproper, hgeo, hconv, hdiv, rfl⟩
  have hbound : ∀ k ∈ ranks, k ≤ N := by
    rintro k ⟨A, S, hproper, _, hconv, _, hk⟩
    let : ProperSpace S.completedLimit.carrier := hproper
    let : Nonempty S.completedLimit.carrier := ⟨S.completedLimit.base⟩
    have hpack := hN (fun j => (A j).metric) (fun j => (A j).point)
      (fun j => (A j).connection) (fun j => (A j).complete)
      (fun j => (A j).sectional_lower) hconv
    rw [← hk]
    exact (minLocalAnglePackingRank_spec hpack).2.2
  have hbounded : BddAbove ranks := ⟨N, hbound⟩
  obtain ⟨A, S, hproper, hgeo, hconv, hdiv, hrank⟩ :=
    Nat.sSup_mem hnonempty hbounded
  let : ProperSpace S.completedLimit.carrier := hproper
  let : Nonempty S.completedLimit.carrier := ⟨S.completedLimit.base⟩
  have hpack := hN (fun j => (A j).metric) (fun j => (A j).point)
    (fun j => (A j).connection) (fun j => (A j).complete)
    (fun j => (A j).sectional_lower) hconv
  have hcurv := RiemannianMetric.curvatureGEnegOne_of_sectional_pointed_limit
    (fun j => (A j).metric) (fun j => (A j).point) (fun j => (A j).connection)
    (fun j => (A j).complete) (fun j => (A j).sectional_lower) hconv
  refine ⟨A, S, hproper, hgeo, hconv, hdiv, hcurv, hpack, ?_,
    (minLocalAnglePackingRank_spec hpack).2.2, ?_⟩
  · intro α hα
    obtain ⟨L, hL⟩ :=
      RiemannianMetric.exists_comparisonAngle_packing_bound_of_sectional_pointed_limit.{0} n hα
    exact ⟨L, hL (fun j => (A j).metric) (fun j => (A j).point)
      (fun j => (A j).connection) (fun j => (A j).complete)
      (fun j => (A j).sectional_lower) hconv⟩
  · intro A' S' hproper' hgeo' hconv' hdiv'
    rw [hrank]
    exact le_csSup hbounded ⟨A', S', hproper', hgeo', hconv', hdiv', rfl⟩

end PoincareConjecture
