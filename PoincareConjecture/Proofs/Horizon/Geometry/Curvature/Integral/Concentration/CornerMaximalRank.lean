import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerModels
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SubsetRank
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.RiemannianLimit








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory Function
open Poincare.GromovHausdorff
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle
open Poincare.Alexandrov
namespace PoincareConjecture



theorem exists_maximal_rank_corner_counterexample_limit
    (m k : ℕ) (hn : 1 ≤ m+k) (θ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ δ H : ℝ,
      (∀ C : ℝ, ∃ A : PointedCornerModel m k δ H, C < A.weightedRatio) →
      ∃ A : ℕ → PointedCornerModel m k δ H,
      ∃ S : CompatiblePointedCompactSystem.{0},
      ∃ K : TopologicalSpace.NonemptyCompacts S.completedLimit.carrier,
        IsExpandingCornerLimit A S K ∧
        Tendsto (fun j => (A j).weightedRatio) atTop atTop ∧
        ComparisonAnglePackingBound S.completedLimit.carrier θ N ∧
        (∀ α : ℝ, 0 < α → ∃ L : ℕ,
          ComparisonAnglePackingBound S.completedLimit.carrier α L) ∧
        minLocalAnglePackingRankOn θ (K : Set S.completedLimit.carrier) ≤ N ∧
        ∀ (A' : ℕ → PointedCornerModel m k δ H)
          (S' : CompatiblePointedCompactSystem.{0})
          (K' : TopologicalSpace.NonemptyCompacts S'.completedLimit.carrier),
          IsExpandingCornerLimit A' S' K' →
          Tendsto (fun j => (A' j).weightedRatio) atTop atTop →
          minLocalAnglePackingRankOn θ (K' : Set S'.completedLimit.carrier) ≤
            minLocalAnglePackingRankOn θ (K : Set S.completedLimit.carrier) := by
  classical
  obtain ⟨N, hN⟩ :=
    RiemannianMetric.exists_comparisonAngle_packing_bound_of_sectional_pointed_limit.{0}
      (m+k) hθ
  refine ⟨N, ?_⟩
  intro δ H hlarge
  let ranks : Set ℕ := {r | ∃ A : ℕ → PointedCornerModel m k δ H,
    ∃ S : CompatiblePointedCompactSystem.{0},
    ∃ K : TopologicalSpace.NonemptyCompacts S.completedLimit.carrier,
      IsExpandingCornerLimit A S K ∧
      Tendsto (fun j => (A j).weightedRatio) atTop atTop ∧
      minLocalAnglePackingRankOn θ (K : Set S.completedLimit.carrier) = r}
  have hnonempty : ranks.Nonempty := by
    obtain ⟨A, _, hdiv⟩ := exists_pointedCornerModels_tendsto_atTop hlarge
    obtain ⟨φ, hφ, S, K, hlim⟩ := exists_subseq_expandingCornerLimit hn A
    exact ⟨_, (fun j => A (φ j)), S, K, hlim, hdiv.comp hφ.tendsto_atTop, rfl⟩
  have hbound : ∀ r ∈ ranks, r ≤ N := by
    rintro r ⟨A, S, K, hlim, _, hrank⟩
    have hpack := hN (fun j => (A j).metric) (fun j => (A j).ambientPoint)
      (fun j => (A j).connection) (fun j => (A j).complete)
      (fun j => (A j).sectional_lower) hlim.2.2.1
    rw [← hrank]
    exact (minLocalAnglePackingRankOn_spec K.nonempty hpack).2.2
  have hbounded : BddAbove ranks := ⟨N, hbound⟩
  obtain ⟨A, S, K, hlim, hdiv, hrank⟩ := Nat.sSup_mem hnonempty hbounded
  have hpack := hN (fun j => (A j).metric) (fun j => (A j).ambientPoint)
    (fun j => (A j).connection) (fun j => (A j).complete)
    (fun j => (A j).sectional_lower) hlim.2.2.1
  refine ⟨A, S, K, hlim, hdiv, hpack, ?_,
    (minLocalAnglePackingRankOn_spec K.nonempty hpack).2.2, ?_⟩
  · intro α hα
    obtain ⟨L, hL⟩ :=
      RiemannianMetric.exists_comparisonAngle_packing_bound_of_sectional_pointed_limit.{0}
        (m+k) hα
    exact ⟨L, hL (fun j => (A j).metric) (fun j => (A j).ambientPoint)
      (fun j => (A j).connection) (fun j => (A j).complete)
      (fun j => (A j).sectional_lower) hlim.2.2.1⟩
  · intro A' S' K' hlim' hdiv'
    rw [hrank]
    exact le_csSup hbounded ⟨A', S', K', hlim', hdiv', rfl⟩

end PoincareConjecture
