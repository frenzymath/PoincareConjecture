import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Hypersurface
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma hessian_mean_curvature (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hreg : 0 < g.inner x (D.gradient f x) (D.gradient f x)) :
    let q := g.inner x (D.gradient f x) (D.gradient f x)
    let u := (Real.sqrt q)⁻¹ • D.gradient f x
    let P := fun v : TangentSpace (𝓡 n) x => v - (g.inner x u v) • u
    (∑ i, D.hessian f x (P (g.orthonormalBasis x i))
      (P (g.orthonormalBasis x i)) / Real.sqrt q) =
        (D.laplacian f x - D.hessian f x u u) / Real.sqrt q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := D.connection (D.gradient f) x
  have hA (v w : TangentSpace (𝓡 n) x) : inner ℝ (A v) w = inner ℝ v (A w) := by
    change g.inner x (A v) w = g.inner x v (A w)
    rw [g.symm x v]
    exact (D.hessian_eq_inner_connection_gradient (hf x) v w).symm.trans
      ((D.hessian_symm hf x v w).trans (D.hessian_eq_inner_connection_gradient (hf x) w v))
  let q := g.inner x (D.gradient f x) (D.gradient f x)
  let u := (Real.sqrt q)⁻¹ • D.gradient f x
  have hu : inner ℝ u u = 1 := by
    change g.inner x u u = 1
    simp only [u, map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = 1
    have hs : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hreg.le
    have hr : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hreg).ne'
    field_simp
    exact hs.symm
  have h := Poincare.LinearAlgebra.trace_orthogonal_restriction
    (g.orthonormalBasis x) A hA u hu
  have hinner (v w : TangentSpace (𝓡 n) x) : inner ℝ v w = g.inner x v w := rfl
  simp only [hinner, A] at h
  dsimp only
  rw [← Finset.sum_div]
  congr 1
  simp_rw [D.hessian_eq_inner_connection_gradient (hf x)]
  rw [D.laplacian_eq_sum_inner_connection_gradient (hf x)]
  exact h

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem integral_hypersurface_bochner_level_cutoff (D : LeviCivitaData g)
    {f : M → ℝ} {η : ℝ → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport (η ∘ f))
    (hreg : ∀ x ∈ tsupport (η ∘ f), 0 < g.inner x (D.gradient f x) (D.gradient f x)) :
    let q := fun x => g.inner x (D.gradient f x) (D.gradient f x)
    let u := fun x => (Real.sqrt (q x))⁻¹ • D.gradient f x
    let P := fun (x : M) (v : TangentSpace (𝓡 n) x) => v - (g.inner x (u x) v) • u x
    let B := fun (x : M) (v w : TangentSpace (𝓡 n) x) =>
      D.hessian f x (P x v) (P x w) / Real.sqrt (q x)
    let H := fun x => ∑ i, B x (g.orthonormalBasis x i) (g.orthonormalBasis x i)
    let G := fun x => (H x) ^ 2 -
      ∑ i, ∑ j, (B x (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2
    (∫ x, η (f x) * (G x - D.ricci x (u x) (u x)) ∂g.volumeMeasure) =
      ∫ x, -(deriv η (f x)) * H x * Real.sqrt (q x) ∂g.volumeMeasure := by
  dsimp only
  have hi := D.integral_hypersurface_bochner (hη.contMDiff.comp hf) hf hc hreg
  dsimp only [Function.comp_apply] at hi
  rw [hi]
  apply integral_congr_ae
  filter_upwards [] with x
  have hchain := D.gradient_comp ((hf x).mdifferentiableAt (by simp))
    (hη.differentiable (by simp) (f x))
  by_cases hx : x ∈ tsupport (η ∘ f)
  · rw [hessian_mean_curvature D hf x (hreg x hx), hchain]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [g.symm x (D.gradient f x), D.inner_gradient,
      D.mvfderiv_gradient_normSq (hf x)]
    simp_rw [D.hessian_eq_inner_connection_gradient (hf x)]
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hs := Real.sq_sqrt (hreg x hx).le
    have hr := (Real.sqrt_pos.2 (hreg x hx)).ne'
    field_simp [(hreg x hx).ne']
    rw [hs]
    ring
  · rw [D.gradient_eq_zero_of_notMem_tsupport hx]
    simp only [map_zero, zero_apply, zero_div, mul_zero, sub_zero]
    by_cases hq : g.inner x (D.gradient f x) (D.gradient f x) = 0
    · simp [hq]
    · have hz := congrArg (fun v => g.inner x v (D.gradient f x)) hchain
      rw [D.gradient_eq_zero_of_notMem_tsupport hx] at hz
      simp only [map_zero, zero_apply, map_smul, smul_apply, smul_eq_mul] at hz
      have hηz : deriv η (f x) = 0 := (mul_eq_zero.mp hz.symm).resolve_right hq
      simp [hηz]

end PoincareConjecture.LeviCivitaData
