import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Spectral.Counting.ChartLocalization
import Mathlib.Algebra.Order.BigOperators.Ring.Finset








set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Counting

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable (D : LeviCivitaData g) (Ω : Set M)
  (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
  {s : Finset M} (ρ : SmoothPartitionOfUnity s (𝓡 n) M (closure Ω))
  (hρc : ∀ i, HasCompactSupport (ρ i : M → ℝ))
  (hρs : ∀ i, tsupport (ρ i : M → ℝ) ⊆
    (chartAt (EuclideanSpace ℝ (Fin n)) (i : M)).source)


def partitionLocalization (i : s) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  chartLocalization D Ω hΩ hc
    (chartAt (EuclideanSpace ℝ (Fin n)) (i : M)).symm
    contMDiffOn_chart_symm contMDiffOn_chart
    (ρ i) (ρ i).contMDiff (hρc i) (hρs i)

set_option backward.isDefEq.respectTransparency false in


theorem exists_partition_norm_bound :
    ∃ C ≥ 0, ∀ u : H1Zero D Ω,
      ‖toDomainL2 D Ω u‖ ^ 2 ≤
        C * ∑ i, ‖partitionLocalization D Ω hΩ hc ρ hρc hρs i
          (toDomainL2 D Ω u)‖ ^ 2 := by
  classical
  have hb (i : s) := exists_norm_testToL2_le_chartToL2 (D := D) (Ω := Ω)
    (chartAt (EuclideanSpace ℝ (Fin n)) (i : M)).symm
    contMDiffOn_chart_symm contMDiffOn_chart (hρc i) (hρs i)
  choose C hC hCb using hb
  refine ⟨∑ i, C i ^ 2, Finset.sum_nonneg (fun i _ => sq_nonneg _), ?_⟩
  intro u
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_le
      (((toDomainL2 D Ω).continuous.norm).pow 2)
      (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        (((partitionLocalization D Ω hΩ hc ρ hρc hρs i).continuous.comp
          (toDomainL2 D Ω).continuous).norm).pow 2))
  | ih f =>
    have hnorm : ‖toDomainL2 D Ω (f : H1Zero D Ω)‖ ≤
        ∑ i, C i * ‖partitionLocalization D Ω hΩ hc ρ hρc hρs i
          (toDomainL2 D Ω (f : H1Zero D Ω))‖ := by
      rw [norm_toDomainL2 hΩ.measurableSet, toL2_coe,
        ← testToL2_sum_mul_partition ρ subset_closure f]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [partitionLocalization, chartLocalization_test]
      exact hCb i (f.mulSmooth (ρ i) (ρ i).contMDiff)
        (f.mulSmooth_support_subset (ρ i) (ρ i).contMDiff)
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    exact hsquare.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ C
      (fun i => ‖partitionLocalization D Ω hΩ hc ρ hρc hρs i
        (toDomainL2 D Ω (f : H1Zero D Ω))‖))

end PoincareConjecture.LeviCivitaData.Dirichlet.Counting
