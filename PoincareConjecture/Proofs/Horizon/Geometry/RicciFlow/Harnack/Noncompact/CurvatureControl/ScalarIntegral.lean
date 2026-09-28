import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.BallVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow



theorem exists_uniform_unitBall_volume_lower_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        (J : Set ℝ) (F : RicciFlow n M J) (a b : ℝ),
        a ≤ b → Icc a b ⊆ interior J →
        (∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus) →
        (∀ t ∈ Icc a b, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc a b, ∀ x : M, (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
          ((F.metric a).volumeMeasure ((F.metric a).ball p 1)).toReal - C * (b - a) ≤
            ((F.metric b).volumeMeasure ((F.metric b).ball p 1)).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_unitBall_scalar_integral_bound.{u} n
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ J F a b hab hJ hD hcomplete hoperator p
  apply F.ball_volume_lower_bound_of_nonnegative_curvatureOperator
    hab hJ hD hcomplete hoperator p 1
  intro t ht
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  apply hbound M (F.metric t) (F.connection t) (hcomplete t ht')
  intro x v w
  exact (by norm_num : (-1 : ℝ) ≤ 0).trans
    ((F.connection t).sectionalCurvature_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t ht' x) v w)


theorem exists_uniform_unitBall_volume_lower_bound_three :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        (J : Set ℝ) (F : RicciFlow 3 M J) (a b : ℝ),
        a ≤ b → Icc a b ⊆ interior J →
        (∀ t ∈ Icc a b, (F.connection t).CurvatureTensorCalculus) →
        (∀ t ∈ Icc a b, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc a b, ∀ x : M, (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
          ((F.metric a).volumeMeasure ((F.metric a).ball p 1)).toReal - C * (b - a) ≤
            ((F.metric b).volumeMeasure ((F.metric b).ball p 1)).toReal := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_unitBall_scalar_integral_bound_three.{u}
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ J F a b hab hJ hD hcomplete hoperator p
  apply F.ball_volume_lower_bound_of_nonnegative_curvatureOperator
    hab hJ hD hcomplete hoperator p 1
  intro t ht
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  apply hbound M (F.metric t) (F.connection t) (hcomplete t ht')
  intro x v w
  exact (by norm_num : (-1 : ℝ) ≤ 0).trans
    ((F.connection t).sectionalCurvature_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t ht' x) v w)

end PoincareConjecture.RicciFlow
