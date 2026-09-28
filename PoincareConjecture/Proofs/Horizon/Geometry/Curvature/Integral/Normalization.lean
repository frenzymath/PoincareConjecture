import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Bochner
import Mathlib.Geometry.Manifold.Algebra.LieGroup










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in
private lemma smooth_div_on_support {φ q : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q)
    (hreg : ∀ x ∈ tsupport φ, q x ≠ 0) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => φ x / q x) := by
  intro x
  by_cases hx : x ∈ tsupport φ
  · simpa only [div_eq_mul_inv, Pi.mul_def] using (hφ x).mul ((hq x).inv₀ (hreg x hx))
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

private lemma inner_gradient_div_on_support (D : LeviCivitaData g)
    {φ q : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q)
    (hreg : ∀ x ∈ tsupport φ, q x ≠ 0)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    g.inner x (D.gradient (fun y => φ y / q y) x) v =
      g.inner x (D.gradient φ x) v / q x -
        φ x / (q x) ^ 2 * g.inner x (D.gradient q x) v := by
  have hw := smooth_div_on_support hφ hq hreg
  have heq : (fun y => q y * (φ y / q y)) = φ := by
    funext y
    by_cases hy : y ∈ tsupport φ
    · field_simp [hreg y hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  by_cases hx : x ∈ tsupport φ
  · have h := D.gradient_mul ((hq x).mdifferentiableAt (by simp))
      ((hw x).mdifferentiableAt (by simp))
    rw [heq] at h
    have hi := congrArg (fun z => g.inner x z v) h
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at hi
    have hqx := hreg x hx
    field_simp
    field_simp at hi
    nlinarith only [hi]
  · have hsupport : tsupport (fun y => φ y / q y) ⊆ tsupport φ := by
      apply closure_mono
      simp only [Function.support_div]
      exact inter_subset_left
    rw [D.gradient_eq_zero_of_notMem_tsupport (fun hy => hx (hsupport hy)),
      D.gradient_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx]
    simp

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]




theorem integral_normalized_bochner (D : LeviCivitaData g)
    {φ f : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hφc : HasCompactSupport φ)
    (hreg : ∀ x ∈ tsupport φ, g.inner x (D.gradient f x) (D.gradient f x) ≠ 0) :
    let q := fun x => g.inner x (D.gradient f x) (D.gradient f x)
    (∫ x, φ x * (((D.laplacian f x) ^ 2 -
        (∑ i, ∑ j, (D.hessian f x
          (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2)) / q x -
      D.laplacian f x * g.inner x (D.gradient q x) (D.gradient f x) / (q x) ^ 2 +
      g.inner x (D.gradient q x) (D.gradient q x) / (2 * (q x) ^ 2) -
      D.ricci x (D.gradient f x) (D.gradient f x) / q x) ∂g.volumeMeasure) =
    ∫ x, g.inner x (D.gradient φ x) (D.gradient q x) / (2 * q x) -
      D.laplacian f x * g.inner x (D.gradient φ x) (D.gradient f x) / q x
      ∂g.volumeMeasure := by
  dsimp only
  let q := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  let w := fun x => φ x / q x
  let A := fun x => w x * ((D.laplacian f x) ^ 2 -
    (∑ i, ∑ j, (D.hessian f x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) -
    D.ricci x (D.gradient f x) (D.gradient f x))
  let B := fun x => (1 / 2 : ℝ) * g.inner x (D.gradient w x) (D.gradient q x) -
    D.laplacian f x * g.inner x (D.gradient w x) (D.gradient f x)
  let C := fun x => (φ x / (q x) ^ 2) *
    (D.laplacian f x * g.inner x (D.gradient q x) (D.gradient f x) -
      (1 / 2 : ℝ) * g.inner x (D.gradient q x) (D.gradient q x))
  have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q := D.contMDiff_inner_gradient hf hf
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w := smooth_div_on_support hφ hq hreg
  have hwc : HasCompactSupport w := by
    apply HasCompactSupport.of_support_subset_isCompact hφc
    intro x hx
    by_contra hx'
    exact hx (by simp [w, image_eq_zero_of_notMem_tsupport hx'])
  have hA : Integrable A g.volumeMeasure := D.integrable_weighted_bochner hw hf hwc
  have hB : Integrable B g.volumeMeasure :=
    ((D.integrable_inner_gradient hw hq hwc).const_mul _).sub
      (((D.continuous_laplacian hf).mul (D.continuous_inner_gradient hw hf)).integrable_of_hasCompactSupport
          (D.hasCompactSupport_inner_gradient hwc f).mul_left)
  have hw₂ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => φ x / (q x) ^ 2) :=
    smooth_div_on_support hφ (hq.pow 2) (fun x hx => pow_ne_zero _ (hreg x hx))
  have hC : Integrable C g.volumeMeasure := by
    apply (hw₂.continuous.mul
      (((D.continuous_laplacian hf).mul (D.continuous_inner_gradient hq hf)).sub
        ((D.continuous_inner_gradient hq hq).const_mul (1 / 2 : ℝ)))).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact hφc
    intro x hx
    by_contra hx'
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'])
  have hi : (∫ x, A x ∂g.volumeMeasure) = ∫ x, B x ∂g.volumeMeasure :=
    D.integral_weighted_bochner hw hf hwc
  calc
    _ = ∫ x, A x - C x ∂g.volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [A, C, w]
      dsimp only [q] at *
      by_cases hx : q x = 0
      · dsimp only [q] at hx
        simp [hx]
      · dsimp only [q] at hx
        field_simp
        ring
    _ = (∫ x, A x ∂g.volumeMeasure) - ∫ x, C x ∂g.volumeMeasure := integral_sub hA hC
    _ = ∫ x, B x - C x ∂g.volumeMeasure := by rw [hi, integral_sub hB hC]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [B, C, w]
      rw [inner_gradient_div_on_support D hφ hq hreg,
        inner_gradient_div_on_support D hφ hq hreg]
      dsimp only [q]
      by_cases hx : q x = 0
      · dsimp only [q] at hx
        simp [hx]
      · dsimp only [q] at hx
        field_simp
        ring

end PoincareConjecture.LeviCivitaData
