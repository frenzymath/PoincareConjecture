import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawEllipticity
import Mathlib.LinearAlgebra.BilinearMap










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)


theorem vector_bilinear_trace_inverse_gram (g : RiemannianMetric n V) (x : V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    (∑ a, B (g.orthonormalBasis x a) (g.orthonormalBasis x a)) =
      ∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ext k
  let q : V →ₗ[ℝ] ℝ := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).toLinearMap
  let b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hb (i : Fin n) : b i = EuclideanSpace.single i 1 :=
    EuclideanSpace.basisFun_apply (Fin n) ℝ i
  have hg : (Matrix.of fun i j => inner ℝ (b i) (b j)) = rawCoordinateGram g x := by
    ext i j
    change g.inner x (b i) (b j) =
      g.inner x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [hb, hb]
  have h := bilinear_sum_basis_eq_inverse_gram (E := TangentSpace (𝓡 n) x) (B.compr₂ q)
    b (g.orthonormalBasis x)
  rw [hg] at h
  simp only [hb] at h
  change (∑ a, q (B (g.orthonormalBasis x a) (g.orthonormalBasis x a))) =
    ∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j *
      q (B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) at h
  change q (∑ a, B (g.orthonormalBasis x a) (g.orthonormalBasis x a)) =
    q (∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
      B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
  simpa only [map_sum, map_smul, smul_eq_mul] using h


def rawHessianBilinear {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (x : V) : V →ₗ[ℝ] V →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ (fun u v =>
    fderiv ℝ (fderiv ℝ X) x u v +
    rawConnectionCoefficient D x v (fderiv ℝ X x u) +
    rawConnectionCoefficient D x u (fderiv ℝ X x v) -
    fderiv ℝ X x (rawConnectionCoefficient D x u v) +
    fderiv ℝ (rawConnectionCoefficient D) x u v (X x) +
    rawConnectionCoefficient D x u (rawConnectionCoefficient D x v (X x)) -
    rawConnectionCoefficient D x (rawConnectionCoefficient D x u v) (X x))
    (by intros; simp only [map_add, add_apply]; module)
    (by intros; simp only [map_smul, smul_apply]; module)
    (by intros; simp only [map_add, add_apply]; module)
    (by intros; simp only [map_smul, smul_apply]; module)

theorem fieldHessian_eq_rawHessianBilinear {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} (hX : ContDiff ℝ ∞ X) (x u v : V) :
    fieldHessian D X x u v = rawHessianBilinear D X x u v :=
  fieldHessian_coordinate_expansion D hX x u v




theorem raw_vector_heat_inverse_gram {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} (hX : ContDiff ℝ ∞ X) (x : V) :
    @Add.add V inferInstance
      (∑ a, fieldHessian D X x (g.orthonormalBasis x a) (g.orthonormalBasis x a))
        (RicciFlow.ricciSharp D x (X x)) =
      @Add.add V inferInstance
        (∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
          rawHessianBilinear D X x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
          (RicciFlow.ricciSharp D x (X x)) := by
  simp only [fieldHessian_eq_rawHessianBilinear D hX]
  rw [vector_bilinear_trace_inverse_gram g x]

end PoincareConjecture.M35.Uniqueness.Heat
