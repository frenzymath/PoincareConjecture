import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Normalization.RoundSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Normalization.RicciNorm
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Normalization.Scalar













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

variable {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] in


theorem ricciNormSq_eq_half_scalar_sq_of_line_at_each_time
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (F : RicciFlow 3 M (Iio 1))
    (hcomplete : ∀ t < 1, MetricComplete (F.metric t))
    (hnonneg : ∀ t < 1, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hline : ∀ t < 1, ∃ γ : ℝ → M, ∀ s r : ℝ,
      (F.metric t).edist (γ s) (γ r) = ENNReal.ofReal |s - r|)
    (t : ℝ) (ht : t < 1) (x : M) :
    (F.connection t).ricciNormSq x = (1 / 2 : ℝ) * (F.connection t).scalarCurvature x ^ 2 := by
  obtain ⟨γ, hγ⟩ := hline t ht
  have hD := hP.curvature.tensor_calculus 3 M (F.metric t) (F.connection t)
  have hRic : (F.connection t).NonnegativeRicciCurvature := by
    intro y v
    exact ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator hD y
      (hnonneg t ht y) v).1
  obtain ⟨hf, hu, _, hz, _⟩ := (F.metric t).busemann_parallel_unit_gradient
    (F.connection t) (hcomplete t ht) hRic hγ
  exact (F.connection t).ricciNormSq_eq_half_scalar_sq_of_parallel_gradient hD hf hu hz x



theorem scalarCurvature_eq_one_div_one_sub_of_line_at_each_time
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (F : RicciFlow 3 M (Iio 1))
    (hcomplete : ∀ t < 1, MetricComplete (F.metric t))
    (hnonneg : ∀ t < 1, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∀ T < 1, ∃ K : ℝ, 0 ≤ K ∧ ∀ t ≤ T, ∀ x,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : ∀ t < 1,
      MetricKappaNoncollapsed (F.metric t) (F.connection t) κ)
    (hline : ∀ t < 1, ∃ γ : ℝ → M, ∀ s r : ℝ,
      (F.metric t).edist (γ s) (γ r) = ENNReal.ofReal |s - r|)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ t < 1, ∀ x : M,
      c / (1 - t) ≤ (F.connection t).scalarCurvature x) :
    ∀ t < 1, ∀ x : M, (F.connection t).scalarCurvature x = 1 / (1 - t) := by
  have hpos (t : ℝ) (ht : t < 1) (x : M) :
      0 < (F.connection t).scalarCurvature x :=
    (div_pos hc (sub_pos.mpr ht)).trans_le (hlower t ht x)
  exact F.scalarCurvature_eq_one_div_one_sub_of_spatially_constant_lower_bound
    (F.scalarCurvature_spatially_constant_of_line_at_each_time
      hP hcomplete hnonneg hbound hκ hpos hline)
    (F.ricciNormSq_eq_half_scalar_sq_of_line_at_each_time hP hcomplete hnonneg hline)
    hc hlower

end PoincareConjecture.RicciFlow
