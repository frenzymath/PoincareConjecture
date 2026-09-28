import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Normalization
import PoincareConjecture.Proofs.Horizon.LinearAlgebra.BilinearForm.OrthogonalRestriction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma hessian_gauss_term (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hreg : 0 < g.inner x (D.gradient f x) (D.gradient f x)) :
    let q := fun y => g.inner y (D.gradient f y) (D.gradient f y)
    let u := (Real.sqrt (q x))⁻¹ • D.gradient f x
    let P := fun v : TangentSpace (𝓡 n) x => v - (g.inner x u v) • u
    let B := fun v w => D.hessian f x (P v) (P w) / Real.sqrt (q x)
    (∑ i, B (g.orthonormalBasis x i) (g.orthonormalBasis x i)) ^ 2 -
      (∑ i, ∑ j, (B (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) =
    ((D.laplacian f x) ^ 2 -
      (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2)) / q x -
      D.laplacian f x * g.inner x (D.gradient q x) (D.gradient f x) / (q x) ^ 2 +
      g.inner x (D.gradient q x) (D.gradient q x) / (2 * (q x) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := D.connection (D.gradient f) x
  have hA (v w : TangentSpace (𝓡 n) x) : inner ℝ (A v) w = inner ℝ v (A w) := by
    change g.inner x (A v) w = g.inner x v (A w)
    rw [g.symm x v]
    exact (D.hessian_eq_inner_connection_gradient (hf x) v w).symm.trans
      ((D.hessian_symm hf x v w).trans (D.hessian_eq_inner_connection_gradient (hf x) w v))
  let q := fun y => g.inner y (D.gradient f y) (D.gradient f y)
  let r := Real.sqrt (q x)
  let v := D.gradient f x
  let u := r⁻¹ • v
  have hr : 0 < r := Real.sqrt_pos.2 hreg
  have hrq : r ^ 2 = q x := Real.sq_sqrt hreg.le
  have hu : inner ℝ u u = 1 := by
    change g.inner x (r⁻¹ • v) (r⁻¹ • v) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    change r⁻¹ * (r⁻¹ * q x) = 1
    rw [← hrq]
    field_simp
  have hgrad : D.gradient q x = (2 : ℝ) • A v := by
    apply (g.inner_isInvertible x).injective
    ext w
    rw [D.inner_gradient]
    change mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x w = _
    rw [D.mvfderiv_gradient_normSq (hf x), D.hessian_symm hf x w,
      D.hessian_eq_inner_connection_gradient (hf x)]
    simp only [map_smul, smul_apply, smul_eq_mul, A, v]
  have hgauss := Poincare.LinearAlgebra.gauss_term_orthogonal_restriction
    (g.orthonormalBasis x) A hA u hu
  have hinner (v w : TangentSpace (𝓡 n) x) : inner ℝ v w = g.inner x v w := rfl
  simp only [hinner, A] at hgauss
  change
    (∑ i, D.hessian f x
      (g.orthonormalBasis x i - (g.inner x u (g.orthonormalBasis x i)) • u)
      (g.orthonormalBasis x i - (g.inner x u (g.orthonormalBasis x i)) • u) / r) ^ 2 -
      (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i - (g.inner x u (g.orthonormalBasis x i)) • u)
        (g.orthonormalBasis x j - (g.inner x u (g.orthonormalBasis x j)) • u) / r) ^ 2) =
    ((D.laplacian f x) ^ 2 -
      (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2)) / q x -
      D.laplacian f x * g.inner x (D.gradient q x) v / (q x) ^ 2 +
      g.inner x (D.gradient q x) (D.gradient q x) / (2 * (q x) ^ 2)
  simp_rw [div_pow, ← Finset.sum_div]
  rw [div_pow, ← sub_div]
  simp_rw [D.hessian_eq_inner_connection_gradient (hf x)]
  rw [hgauss]
  have hlap : D.laplacian f x = ∑ i, inner ℝ (A (g.orthonormalBasis x i))
      (g.orthonormalBasis x i) := D.laplacian_eq_sum_inner_connection_gradient (hf x)
  simp only [hinner, A] at hlap
  rw [hlap, hgrad]
  simp only [u, map_smul, smul_apply, smul_eq_mul, A]
  rw [← hrq]
  field_simp

private lemma ricci_smul_self (D : LeviCivitaData g)
    (x : M) (c : ℝ) (v : TangentSpace (𝓡 n) x) :
    D.ricci x (c • v) (c • v) = c ^ 2 * D.ricci x v v := by
  unfold ricci
  simp_rw [← D.curvatureTensor_bilinear_first_third_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]
  ring




lemma inner_connection_unitNormal (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hreg : 0 < g.inner x (D.gradient f x) (D.gradient f x))
    (v w : TangentSpace (𝓡 n) x) (hw : g.inner x (D.gradient f x) w = 0) :
    g.inner x (D.connection
      (fun y => (Real.sqrt (g.inner y (D.gradient f y) (D.gradient f y)))⁻¹ •
        D.gradient f y) x v) w =
      D.hessian f x v w / Real.sqrt (g.inner x (D.gradient f x) (D.gradient f x)) := by
  let q := fun y => g.inner y (D.gradient f y) (D.gradient f y)
  let a := fun y => (Real.sqrt (q y))⁻¹
  have ha : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a x :=
    (((Real.contDiffAt_sqrt hreg.ne').contMDiffAt.comp x
      (D.contMDiff_inner_gradient hf hf x)).inv₀
        (Real.sqrt_pos.2 hreg).ne').mdifferentiableAt (by simp)
  have hg := (D.contMDiff_gradient hf x).mdifferentiableAt (by simp)
  change g.inner x (D.connection (a • D.gradient f) x v) w = _
  rw [D.connection.isCovariantDerivativeOn.leibniz hg ha]
  simp only [ContinuousLinearMap.smulRight_apply, map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul, hw, mul_zero, add_zero]
  rw [D.hessian_eq_inner_connection_gradient (hf x)]
  simp only [a, q, div_eq_mul_inv, mul_comm]

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]





theorem integral_hypersurface_bochner (D : LeviCivitaData g)
    {φ f : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hφc : HasCompactSupport φ)
    (hreg : ∀ x ∈ tsupport φ, 0 < g.inner x (D.gradient f x) (D.gradient f x)) :
    let q := fun x => g.inner x (D.gradient f x) (D.gradient f x)
    let u := fun x => (Real.sqrt (q x))⁻¹ • D.gradient f x
    let P := fun (x : M) (v : TangentSpace (𝓡 n) x) => v - (g.inner x (u x) v) • u x
    let B := fun (x : M) (v w : TangentSpace (𝓡 n) x) =>
      D.hessian f x (P x v) (P x w) / Real.sqrt (q x)
    let G := fun x => (∑ i, B x (g.orthonormalBasis x i) (g.orthonormalBasis x i)) ^ 2 -
      ∑ i, ∑ j, (B x (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2
    (∫ x, φ x * (G x - D.ricci x (u x) (u x)) ∂g.volumeMeasure) =
      ∫ x, g.inner x (D.gradient φ x) (D.gradient q x) / (2 * q x) -
        D.laplacian f x * g.inner x (D.gradient φ x) (D.gradient f x) / q x
          ∂g.volumeMeasure := by
  dsimp only
  rw [← D.integral_normalized_bochner hφ hf hφc (fun x hx => (hreg x hx).ne')]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport φ
  · rw [hessian_gauss_term D hf x (hreg x hx), ricci_smul_self]
    have hs := Real.sq_sqrt (hreg x hx).le
    rw [inv_pow, hs]
    ring
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [hφx, zero_mul]

end PoincareConjecture.LeviCivitaData
