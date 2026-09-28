import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Identities
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace LeviCivitaData

theorem scalar_nonnegative_of_nonnegative_curvatureOperator
    {g : RiemannianMetric 2 M} (D : LeviCivitaData g) (x : M)
    (hoperator : D.NonnegativeCurvatureOperator x) :
    0 ≤ D.scalarCurvature x := by
  unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x hoperator _ _

theorem scalar_positive_of_nonflat_surface {g : RiemannianMetric 2 M}
    (D : LeviCivitaData g) (x : M) (hoperator : D.NonnegativeCurvatureOperator x)
    (hnonflat : D.curvatureTensorNorm x ≠ 0) : 0 < D.scalarCurvature x := by
  refine lt_of_le_of_ne (D.scalar_nonnegative_of_nonnegative_curvatureOperator x hoperator) ?_
  intro hzero
  apply hnonflat
  have hz (u v w z : TangentSpace (𝓡 2) x) :
      D.curvatureTensor x u v w z = 0 := by
    rw [D.curvatureTensor_eq_half_scalarCurvature, ← hzero]
    simp
  simp [LeviCivitaData.curvatureTensorNorm, hz]

theorem ricci_lower_bound_of_surface_conservation {g : RiemannianMetric 2 M}
    (D : LeviCivitaData g) (f : M → ℝ) (α : ℝ) (hα : 0 < α)
    (hoperator : ∀ x : M, D.NonnegativeCurvatureOperator x)
    (hnonflat : ∃ x : M, D.curvatureTensorNorm x ≠ 0) (A C : ℝ)
    (hA : ∀ x : M, D.scalarCurvature x * Real.exp (-f x) = A)
    (hC : ∀ x : M, D.scalarCurvature x +
      g.inner x (g.gradient f x) (g.gradient f x) - α * f x = C) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      k * g.inner x v v ≤ D.ricci x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨p, hp⟩ := hnonflat
  have hp := D.scalar_positive_of_nonflat_surface p (hoperator p) hp
  have hApos : 0 < A := by
    rw [← hA p]
    exact mul_pos hp (Real.exp_pos _)
  have hfn (x : M) : -C / α ≤ f x := by
    apply (div_le_iff₀ hα).mpr
    have hn : 0 ≤ g.inner x (g.gradient f x) (g.gradient f x) :=
      show 0 ≤ inner ℝ (g.gradient f x) (g.gradient f x) from real_inner_self_nonneg
    have hR := D.scalar_nonnegative_of_nonnegative_curvatureOperator x (hoperator x)
    linarith [hC x]
  have hR (x : M) : A * Real.exp (-C / α) ≤ D.scalarCurvature x := by
    calc
      A * Real.exp (-C / α) ≤ A * Real.exp (f x) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hfn x)) hApos.le
      _ = D.scalarCurvature x := by
        rw [← hA x, mul_assoc, ← Real.exp_add]
        simp
  refine ⟨A * Real.exp (-C / α) / 2, div_pos (mul_pos hApos (Real.exp_pos _))
    (by norm_num), fun x v => ?_⟩
  rw [D.ricci_eq_half_scalarCurvature_mul_inner]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hR x) (by norm_num))
    (show 0 ≤ inner ℝ v v from real_inner_self_nonneg)

end LeviCivitaData

namespace GradientShrinkingSolitonData

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem scalar_nonnegative (S : GradientShrinkingSolitonData 2 M) (x : M) :
    0 ≤ S.connection.scalarCurvature x :=
  S.connection.scalar_nonnegative_of_nonnegative_curvatureOperator x (S.nonnegative_curvature x)

theorem scalar_positive_somewhere (S : GradientShrinkingSolitonData 2 M) :
    ∃ x : M, 0 < S.connection.scalarCurvature x := by
  obtain ⟨x, hx⟩ := S.nonflat
  exact ⟨x, S.connection.scalar_positive_of_nonflat_surface x (S.nonnegative_curvature x) hx⟩

theorem ricci_lower_bound_of_conservation (S : GradientShrinkingSolitonData 2 M)
    (A C : ℝ)
    (hA : ∀ x : M, S.connection.scalarCurvature x * Real.exp (-S.potential x) = A)
    (hC : ∀ x : M, S.connection.scalarCurvature x +
      S.metric.inner x (S.metric.gradient S.potential x) (S.metric.gradient S.potential x) -
        S.potential x = C) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      k * S.metric.inner x v v ≤ S.connection.ricci x v v := by
  exact S.connection.ricci_lower_bound_of_surface_conservation S.potential 1 zero_lt_one
    S.nonnegative_curvature S.nonflat A C hA (by simpa using hC)

end GradientShrinkingSolitonData

end PoincareConjecture
