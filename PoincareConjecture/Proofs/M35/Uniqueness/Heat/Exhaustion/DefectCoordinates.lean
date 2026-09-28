import PoincareConjecture.Proofs.M35.Uniqueness.KillingDefectDivergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.Dual
import Mathlib.LinearAlgebra.Multilinear.Curry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem inverseCoefficients_eq_orthonormal_sum (g : RiemannianMetric n V)
    (x : V) (i j : Fin n) :
    g.inverseCoefficients x i j =
      ∑ k, EuclideanSpace.proj i (g.orthonormalBasis x k) *
        EuclideanSpace.proj j (g.orthonormalBasis x k) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := congrArg (fun v : TangentSpace (𝓡 n) x => EuclideanSpace.proj j v)
    ((g.orthonormalBasis x).sum_repr' ((g.inner x).inverse (EuclideanSpace.proj i)))
  have hp (k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      inner ℝ (g.orthonormalBasis x k) ((g.inner x).inverse (EuclideanSpace.proj i)) =
        EuclideanSpace.proj i (g.orthonormalBasis x k) := by
    change g.inner x (g.orthonormalBasis x k) ((g.inner x).inverse (EuclideanSpace.proj i)) = _
    rw [g.symm, (g.inner_isInvertible x).self_apply_inverse]
    rfl
  simpa only [OrthonormalBasis.repr_apply_apply, hp, map_sum, map_smul,
    smul_eq_mul, RiemannianMetric.inverseCoefficients, PiLp.proj_apply] using h.symm

theorem bilinear_trace_inverseCoefficients (g : RiemannianMetric n V) (x : V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (∑ k, B (g.orthonormalBasis x k) (g.orthonormalBasis x k)) =
      ∑ i, ∑ j, g.inverseCoefficients x i j * B (e i) (e j) := by
  have hexp (u v : V) : B u v = ∑ i, ∑ j, (u i * v j) * B (e i) (e j) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr u,
      ← (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  conv_lhs => arg 2; ext k; rw [hexp]
  simp_rw [inverseCoefficients_eq_orthonormal_sum, PiLp.proj_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem threeTensor_trace_first_inverseCoefficients (g : RiemannianMetric n V)
    {H : V → (Fin 3 → V) → ℝ} (hH : IsSmoothCovariantTensor H) (x w : V) :
    (∑ k, H x ![g.orthonormalBasis x k, g.orthonormalBasis x k, w]) =
      ∑ i, ∑ j, g.inverseCoefficients x i j * H x ![e i, e j, w] := by
  obtain ⟨A, hA⟩ : ∃ A : MultilinearMap ℝ (fun _ : Fin 3 => V) ℝ,
    ∀ v, H x v = A v := hH.1 x
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => A ![u, v, w])
    (fun u v z => A.cons_add ![z, w] u v)
    (fun c u v => by convert! A.cons_smul ![v, w] c u using 1)
    (fun u v z => (A.curryLeft u).cons_add ![w] v z)
    (fun c u v => by convert! (A.curryLeft u).cons_smul ![w] c v using 1)
  simp only [hA]
  exact bilinear_trace_inverseCoefficients g x B

theorem threeTensor_trace_last_inverseCoefficients (g : RiemannianMetric n V)
    {H : V → (Fin 3 → V) → ℝ} (hH : IsSmoothCovariantTensor H) (x w : V) :
    (∑ k, H x ![w, g.orthonormalBasis x k, g.orthonormalBasis x k]) =
      ∑ i, ∑ j, g.inverseCoefficients x i j * H x ![w, e i, e j] := by
  obtain ⟨A, hA⟩ : ∃ A : MultilinearMap ℝ (fun _ : Fin 3 => V) ℝ,
    ∀ v, H x v = A v := hH.1 x
  simp only [hA]
  exact bilinear_trace_inverseCoefficients g x (bilinearOfTwoTensor (A.curryLeft w))

theorem vector_component_eq_inverse_metric_pair (g : RiemannianMetric n V)
    (x z : V) (k : Fin n) :
    z k = ∑ l, g.inverseCoefficients x k l * g.inner x z (e l) := by
  have hexp : (g.inner x).inverse (EuclideanSpace.proj k) =
      ∑ l, g.inverseCoefficients x k l • e l := by
    simpa only [RiemannianMetric.inverseCoefficients, PiLp.proj_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr
        ((g.inner x).inverse (EuclideanSpace.proj k))).symm
  calc
    _ = g.inner x ((g.inner x).inverse (EuclideanSpace.proj k)) z := by
      rw [(g.inner_isInvertible x).self_apply_inverse]
      rfl
    _ = g.inner x z ((g.inner x).inverse (EuclideanSpace.proj k)) := g.symm _ _ _
    _ = _ := by rw [hexp]; simp only [map_sum, map_smul, smul_eq_mul]

theorem vector_heat_component_eq_defect_coordinates
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (hX : ContDiff ℝ ∞ X) (x : V) (k : Fin n) :
    (@Add.add V inferInstance
      (∑ a, fieldHessian D X x (g.orthonormalBasis x a) (g.orthonormalBasis x a))
      (RicciFlow.ricciSharp D x (X x))) k =
      ∑ l, g.inverseCoefficients x k l *
        ((∑ i, ∑ j, g.inverseCoefficients x i j *
          D.covariantTensorDerivative (killingDefectTensor D X) x ![e i, e j, e l]) -
        (1 / 2 : ℝ) * ∑ i, ∑ j, g.inverseCoefficients x i j *
          D.covariantTensorDerivative (killingDefectTensor D X) x ![e l, e i, e j]) := by
  have hH := M04.isSmoothCovariantTensor_covariantTensorDerivative D
    (isSmoothCovariantTensor_killingDefectTensor D X hX)
  rw [vector_component_eq_inverse_metric_pair g x]
  apply Finset.sum_congr rfl
  intro l _
  rw [vector_heat_pair_eq_defect_derivative_trace D X hX,
    threeTensor_trace_first_inverseCoefficients g hH,
    threeTensor_trace_last_inverseCoefficients g hH]

end PoincareConjecture.M35.Uniqueness.Heat
