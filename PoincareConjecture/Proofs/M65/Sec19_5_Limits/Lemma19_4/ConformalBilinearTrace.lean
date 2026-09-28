import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalConnectionTrace
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

namespace PoincareConjecture.M65Gauss

def secondFundamentalFormBilinear {m n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}
    (D : LeviCivitaData g) (Ds : LeviCivitaData h)
    (f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.mk₂ ℝ (secondFundamentalForm D Ds f x)
    (by intros; simp only [secondFundamentalForm, covariantHessianMap, map_add, add_apply]; abel)
    (by intros; simp only [secondFundamentalForm, covariantHessianMap, map_smul,
        smul_apply, smul_add, smul_sub])
    (by intros; simp only [secondFundamentalForm, covariantHessianMap, map_add]; abel)
    (by intros; simp only [secondFundamentalForm, covariantHessianMap, map_smul,
        smul_add, smul_sub])

theorem bilinear_conformal_trace
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {h : RiemannianMetric 2 LoopPlane} (x : LoopPlane)
    (B : LoopPlane →ₗ[ℝ] LoopPlane →ₗ[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hconf : ∀ i j : Fin 2,
      h.inner x (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ j) = if i = j then c else 0) :
    (∑ i, B (h.orthonormalBasis x i) (h.orthonormalBasis x i)) =
      c⁻¹ • ∑ i : Fin 2, B (EuclideanSpace.basisFun (Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : LoopPlane → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) x) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have he (i : Fin 2) : e i = EuclideanSpace.basisFun (Fin 2) ℝ i := rfl
  have hG : Matrix.of (fun i j : Fin 2 => ⟪e i, e j⟫_ℝ) =
      c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    change h.inner x (EuclideanSpace.basisFun (Fin 2) ℝ i)
      (EuclideanSpace.basisFun (Fin 2) ℝ j) = _
    simpa only [Matrix.of_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      using hconf i j
  let : Invertible c := invertibleOfNonzero hc.ne'
  have hGi : (Matrix.of (fun i j : Fin 2 => ⟪e i, e j⟫_ℝ))⁻¹ =
      c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hG, Matrix.inv_smul (1 : Matrix (Fin 2) (Fin 2) ℝ) c (by simp), inv_one,
      invOf_eq_inv]
  apply Module.eval_apply_injective ℝ
  apply LinearMap.ext
  intro L
  change L (∑ i, B (h.orthonormalBasis x i) (h.orthonormalBasis x i)) =
    L (c⁻¹ • ∑ i : Fin 2, B (EuclideanSpace.basisFun (Fin 2) ℝ i)
      (EuclideanSpace.basisFun (Fin 2) ℝ i))
  simp only [map_sum, map_smul, smul_eq_mul]
  let A : TangentSpace (𝓡 2) x →ₗ[ℝ] TangentSpace (𝓡 2) x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => L (B u v))
      (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have ht := bilinear_sum_basis_eq_inverse_gram A e (h.orthonormalBasis x)
  rw [hGi] at ht
  simpa only [smul_eq_mul,
    Matrix.smul_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    ← Finset.mul_sum, A, LinearMap.mk₂_apply, he] using ht

end PoincareConjecture.M65Gauss
