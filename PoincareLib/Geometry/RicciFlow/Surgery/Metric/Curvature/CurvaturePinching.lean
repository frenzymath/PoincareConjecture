import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Local
import PoincareLib.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Curvature.PinchingTransport

/-!
# Pinching on a region of nonnegative sectional curvature

Morgan--Tian Theorem 13.2 and Proposition 13.14, pp.332 and 340.
On the positive cap the negative part vanishes and the scalar curvature
is nonnegative. These consequences use the actual chosen connection,
the metric's orthonormal basis and the infimum of its sectional values.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.MetricSurgery

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem sectional_eq_tensor_of_orthonormal (D : LeviCivitaData g) (x : M)
    {v w : TangentSpace (𝓡 3) x} (hvw : LeviCivitaData.IsOrthonormalPair g x v w) :
    D.sectionalCurvature x v w = D.curvatureTensor x v w v w := by
  simp only [LeviCivitaData.sectionalCurvature, hvw.1, hvw.2.1, hvw.2.2,
    one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one]

theorem scalar_nonneg_of_orthonormal_sectional_nonneg (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x v w → 0 ≤ D.sectionalCurvature x v w) :
    0 ≤ D.scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  by_cases hij : i = j
  · subst j
    simp [LeviCivitaData.curvatureTensor, RicciFlowAnalysis.curvature_self]
  · have hpair : LeviCivitaData.IsOrthonormalPair g x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j) := by
      exact ⟨(g.orthonormalBasis x).inner_eq_one i,
        (g.orthonormalBasis x).inner_eq_one j,
        (g.orthonormalBasis x).inner_eq_zero hij⟩
    rw [← sectional_eq_tensor_of_orthonormal D x hpair]
    exact hsec _ _ hpair

theorem leastSectional_nonneg_of_orthonormal_sectional_nonneg
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x v w → 0 ≤ D.sectionalCurvature x v w) :
    0 ≤ D.leastSectionalCurvature x := by
  classical
  let S : Set ℝ := {k | ∃ v w : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x v w ∧ k = D.curvatureTensor x v w v w}
  change 0 ≤ sInf S
  by_cases hS : S.Nonempty
  · apply le_csInf hS
    rintro k ⟨v, w, hvw, rfl⟩
    rw [← sectional_eq_tensor_of_orthonormal D x hvw]
    exact hsec v w hvw
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sInf_empty]

theorem negativeCurvaturePart_eq_zero_of_orthonormal_sectional_nonneg
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x v w → 0 ≤ D.sectionalCurvature x v w) :
    D.negativeCurvaturePart x = 0 := by
  exact max_eq_right (neg_nonpos.mpr
    (leastSectional_nonneg_of_orthonormal_sectional_nonneg D x hsec))

theorem surgeryPinchedOn_of_orthonormal_sectional_nonneg
    (D : LeviCivitaData g) {t : ℝ} (ht : 0 ≤ t) {U : Set M}
    (hsec : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x v w → 0 ≤ D.sectionalCurvature x v w) :
    SurgeryPinchedOn D t U := by
  refine ⟨ht, fun x hx => pinching_scalar_lower_bound_of_nonneg ht
    (scalar_nonneg_of_orthonormal_sectional_nonneg D x (hsec x hx)), ?_⟩
  intro x hx hneg
  rw [negativeCurvaturePart_eq_zero_of_orthonormal_sectional_nonneg D x (hsec x hx)] at hneg
  exact (lt_irrefl 0 hneg).elim

end PoincareMT.MetricSurgery
