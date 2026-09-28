import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction
import Mathlib.Algebra.QuadraticDiscriminant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem LeviCivitaData.ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v) :
    D.ricciNormSq x ≤ (D.scalarCurvature x) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hD.2.1.1 x
  let B := bilinearOfTwoTensor A
  have hB (u v : TangentSpace (𝓡 n) x) : B u v = D.ricci x u v := by
    simpa only [B, bilinearOfTwoTensor_apply, LeviCivitaData.ricciEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one] using (hA ![u, v]).symm
  have hsym (u v : TangentSpace (𝓡 n) x) : B u v = B v u := by
    rw [hB, hB]
    exact (hD.2.2.2.1 x u v u v).2.2.2
  have hsq (u v : TangentSpace (𝓡 n) x) :
      (D.ricci x u v) ^ 2 ≤ D.ricci x u u * D.ricci x v v := by
    have hq : ∀ z : ℝ,
        0 ≤ B u u * (z * z) + (2 * B u v) * z + B v v := by
      intro z
      have h : 0 ≤ B (z • u + v) (z • u + v) := hB _ _ ▸ hRic _
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul] at h
      rw [hsym v u] at h
      nlinarith
    have hd := discrim_le_zero hq
    simp only [discrim, hB] at hd
    nlinarith
  let b := g.orthonormalBasis x
  change (∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2) ≤
    (∑ i, D.ricci x (b i) (b i)) ^ 2
  calc
    _ ≤ ∑ i, ∑ j, D.ricci x (b i) (b i) * D.ricci x (b j) (b j) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hsq (b i) (b j)))
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]

theorem RicciFlow.deriv_scalarCurvature_le_laplacian_add_sq_of_ricci_nonneg
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection t).ricci x v v) :
    deriv (fun s => (F.connection s).scalarCurvature x) t ≤
      (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * ((F.connection t).scalarCurvature x) ^ 2 := by
  have hd := (hC.scalar_evolution n M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  rw [hd.deriv]
  have hnorm := (F.connection t).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) x hRic
  linarith

theorem RicciFlow.deriv_scalarCurvature_le_laplacian_add_sq_of_nonnegative_curvatureOperator
    [T2Space M] (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hoperator : (F.connection t).NonnegativeCurvatureOperator x) :
    deriv (fun s => (F.connection s).scalarCurvature x) t ≤
      (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * ((F.connection t).scalarCurvature x) ^ 2 :=
  F.deriv_scalarCurvature_le_laplacian_add_sq_of_ricci_nonneg hC ht x
    (fun v => ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) x hoperator v).1)

end PoincareConjecture
