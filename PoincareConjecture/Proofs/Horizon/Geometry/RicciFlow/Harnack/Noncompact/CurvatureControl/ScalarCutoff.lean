import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Extension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem deriv_cutoff_mul_scalarCurvature_le_at_max
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (φ : ℝ → M → ℝ)
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (φ t))
    (hφtime : DifferentiableAt ℝ (fun s => φ s x) t)
    (hφpos : 0 < φ t x)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection t).ricci x v v)
    (hmax : IsLocalMax (fun y => φ t y * (F.connection t).scalarCurvature y) x) :
    deriv (fun s => φ s x * (F.connection s).scalarCurvature x) t ≤
      2 * (F.connection t).scalarCurvature x *
        (φ t x * (F.connection t).scalarCurvature x) +
      (F.connection t).scalarCurvature x *
        (deriv (fun s => φ s x) t - (F.connection t).laplacian (φ t) x +
          2 * (F.metric t).inner x ((F.connection t).gradient (φ t) x)
            ((F.connection t).gradient (φ t) x) / φ t x) := by
  let D := F.connection t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hR := hD.contMDiff_scalarCurvature
  have hprod := hφ.mul hR
  have hgrad := congrArg (fun A : TangentSpace (𝓡 n) x →L[ℝ] ℝ =>
    A (D.gradient (φ t) x)) (LeviCivitaData.mvfderiv_eq_zero_of_isLocalMax hprod hmax)
  change mvfderiv (𝓡 n) (fun y => φ t y * D.scalarCurvature y) x
    (D.gradient (φ t) x) = 0 at hgrad
  rw [mvfderiv_fun_mul ((hφ x).mdifferentiableAt (by simp))
    ((hR x).mdifferentiableAt (by simp))] at hgrad
  simp only [add_apply, smul_apply, smul_eq_mul, ← D.inner_gradient] at hgrad
  rw [(F.metric t).symm x (D.gradient D.scalarCurvature x) (D.gradient (φ t) x)] at hgrad
  have hlap := D.laplacian_nonpos_of_isLocalMax hprod hmax
  change D.laplacian (fun y => φ t y * D.scalarCurvature y) x ≤ 0 at hlap
  rw [D.laplacian_mul hφ hR x] at hlap
  have hd := (hC.scalar_evolution n M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  rw [deriv_fun_mul hφtime hd.differentiableAt, hd.deriv]
  have hnorm := D.ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg hD x hRic
  have hnorm' := mul_le_mul_of_nonneg_left hnorm hφpos.le
  have hcross :
      2 * (F.metric t).inner x (D.gradient (φ t) x) (D.gradient D.scalarCurvature x) =
        -(D.scalarCurvature x * (2 * (F.metric t).inner x
          (D.gradient (φ t) x) (D.gradient (φ t) x) / φ t x)) := by
    field_simp [ne_of_gt hφpos]
    nlinarith
  dsimp only [D] at hnorm' hcross hlap
  rw [hcross] at hlap
  nlinarith

theorem deriv_cutoff_mul_scalarCurvature_le_linear_at_max
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (φ : ℝ → M → ℝ)
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (φ t))
    (hφtime : DifferentiableAt ℝ (fun s => φ s x) t)
    (hφpos : 0 < φ t x)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection t).ricci x v v)
    (hmax : IsLocalMax (fun y => φ t y * (F.connection t).scalarCurvature y) x)
    {Q A : ℝ} (hQ : (F.connection t).scalarCurvature x ≤ Q) (hA : 0 ≤ A)
    (hcutoff : deriv (fun s => φ s x) t - (F.connection t).laplacian (φ t) x +
      2 * (F.metric t).inner x ((F.connection t).gradient (φ t) x)
        ((F.connection t).gradient (φ t) x) / φ t x ≤ A) :
    deriv (fun s => φ s x * (F.connection s).scalarCurvature x) t ≤
      2 * Q * (φ t x * (F.connection t).scalarCurvature x) + Q * A := by
  have hR : 0 ≤ (F.connection t).scalarCurvature x :=
    Finset.sum_nonneg (fun _ _ => hRic _)
  apply (F.deriv_cutoff_mul_scalarCurvature_le_at_max
    hC ht x φ hφ hφtime hφpos hRic hmax).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by norm_num))
      (mul_nonneg hφpos.le hR)
  · exact (mul_le_mul_of_nonneg_left hcutoff hR).trans
      (mul_le_mul_of_nonneg_right hQ hA)

theorem deriv_cutoff_mul_scalarCurvature_le_at_max_on_open [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (φ : ℝ → M → ℝ)
    {U : Set M} (hU : IsOpen U) (hx : x ∈ U)
    (hφ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (φ t) U)
    (hφtime : DifferentiableAt ℝ (fun s => φ s x) t)
    (hφpos : 0 < φ t x)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection t).ricci x v v)
    (hmax : IsLocalMax (fun y => φ t y * (F.connection t).scalarCurvature y) x) :
    deriv (fun s => φ s x * (F.connection s).scalarCurvature x) t ≤
      2 * (F.connection t).scalarCurvature x *
        (φ t x * (F.connection t).scalarCurvature x) +
      (F.connection t).scalarCurvature x *
        (deriv (fun s => φ s x) t - (F.connection t).laplacian (φ t) x +
          2 * (F.metric t).inner x ((F.connection t).gradient (φ t) x)
            ((F.connection t).gradient (φ t) x) / φ t x) := by
  obtain ⟨f, hf, heq⟩ := Poincare.Manifold.exists_contMDiff_eq_near hU hφ hx

  let ψ : ℝ → M → ℝ := fun s y => φ s y + f y - φ t y
  have hψ : ψ t = f := by
    funext y
    dsimp only [ψ]
    ring
  have hψx (s : ℝ) : ψ s x = φ s x := by
    dsimp only [ψ]
    rw [heq.self_of_nhds]
    ring
  have hlocal : IsLocalMax
      (fun y => ψ t y * (F.connection t).scalarCurvature y) x := by
    apply hmax.congr
    filter_upwards [heq] with y hy
    rw [hψ, hy]
  have hgrad : (F.connection t).gradient f x = (F.connection t).gradient (φ t) x := by
    unfold LeviCivitaData.gradient
    rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
  have h := F.deriv_cutoff_mul_scalarCurvature_le_at_max hC ht x ψ
    (by simpa only [hψ] using hf)
    (by simpa only [hψx] using hφtime)
    (by simpa only [hψx] using hφpos) hRic hlocal
  simpa only [hψx, hψ, hgrad,
    (F.connection t).laplacian_eq_of_eventuallyEq heq] using h

theorem deriv_cutoff_mul_scalarCurvature_le_linear_at_max_on_open [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (φ : ℝ → M → ℝ)
    {U : Set M} (hU : IsOpen U) (hx : x ∈ U)
    (hφ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (φ t) U)
    (hφtime : DifferentiableAt ℝ (fun s => φ s x) t)
    (hφpos : 0 < φ t x)
    (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection t).ricci x v v)
    (hmax : IsLocalMax (fun y => φ t y * (F.connection t).scalarCurvature y) x)
    {Q A : ℝ} (hQ : (F.connection t).scalarCurvature x ≤ Q) (hA : 0 ≤ A)
    (hcutoff : deriv (fun s => φ s x) t - (F.connection t).laplacian (φ t) x +
      2 * (F.metric t).inner x ((F.connection t).gradient (φ t) x)
        ((F.connection t).gradient (φ t) x) / φ t x ≤ A) :
    deriv (fun s => φ s x * (F.connection s).scalarCurvature x) t ≤
      2 * Q * (φ t x * (F.connection t).scalarCurvature x) + Q * A := by
  have hR : 0 ≤ (F.connection t).scalarCurvature x :=
    Finset.sum_nonneg (fun _ _ => hRic _)
  apply (F.deriv_cutoff_mul_scalarCurvature_le_at_max_on_open
    hC ht x φ hU hx hφ hφtime hφpos hRic hmax).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by norm_num))
      (mul_nonneg hφpos.le hR)
  · exact (mul_le_mul_of_nonneg_left hcutoff hR).trans
      (mul_le_mul_of_nonneg_right hQ hA)

end PoincareConjecture.RicciFlow
