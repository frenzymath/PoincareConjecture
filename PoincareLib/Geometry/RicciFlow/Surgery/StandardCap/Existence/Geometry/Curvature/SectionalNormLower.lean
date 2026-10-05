import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.SectionalTests
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.ConnectionScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.FixedExtension
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.RiemannRegularity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci

/-!
# A full-norm sectional lower bound

Normalize only the test pairs in the actual metric tangent inner product.
The alternating-form reduction then covers every pair, including the
dependent ones. This is the bounded-below input to the noncompact
comparison for Morgan-Tian Lemma 12.6, pp. 297-298.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M34

open M04

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The negative full tensor norm is a sectional lower bound in every
plane (Lemma 12.6, pp. 297-298). -/
theorem neg_curvatureTensorNorm_mul_metricGram_le
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    -D.curvatureTensorNorm x * metricGram g x u v ≤ D.curvatureTensor x u v u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply sectional_lower_of_surjective_linearMap D x (LinearMap.id :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x) Function.surjective_id
  intro p q hp hq hpq
  have hpp : g.inner x p p = 1 := by
    change inner ℝ p p = 1
    rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hqq : g.inner x q q = 1 := by
    change inner ℝ q q = 1
    rw [real_inner_self_eq_norm_sq, hq, one_pow]
  have hpq' : g.inner x p q = 0 := hpq
  have hN : g.tensorNorm D.riemannEvaluation x = D.curvatureTensorNorm x :=
    D.curvatureDerivativeNorm_zero x
  have hsq := tensorEvaluation_sq_le_tensorNorm g
    (isSmoothCovariantTensor_riemannEvaluation D) x ![p, q, p, q]
  simp only [LeviCivitaData.riemannEvaluation, hN, Fin.prod_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hpp, hqq, mul_one] at hsq
  have hlow := (abs_le.mp (abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _))).1
  simpa only [LinearMap.id_apply, metricGram, hpp, hqq, hpq', one_mul,
    zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_one] using hlow

/-- Divide the tensor lower bound by the positive Gram determinant of an
independent plane (Lemma 12.6, pp. 297-298). -/
theorem neg_curvatureTensorNorm_le_sectionalRayleigh
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x)
    (hgram : 0 < metricGram g x u v) :
    -D.curvatureTensorNorm x ≤ D.curvatureTensor x u v u v / metricGram g x u v :=
  (le_div_iff₀ hgram).mpr (neg_curvatureTensorNorm_mul_metricGram_le D x u v)

end PoincareMT.M34
