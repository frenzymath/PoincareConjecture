import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.HypersurfaceFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Localization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in
private theorem smooth_div_sqrt_on_support {φ q : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q)
    (hreg : ∀ x ∈ tsupport φ, 0 < q x) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => φ x / Real.sqrt (q x)) := by
  intro x
  by_cases hx : x ∈ tsupport φ
  · simpa only [div_eq_mul_inv, Function.comp_apply, Pi.mul_def] using (hφ x).mul
      (((Real.contDiffAt_sqrt (hreg x hx).ne').contMDiffAt.comp x (hq x)).inv₀
        (Real.sqrt_pos.2 (hreg x hx)).ne')
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

private theorem inner_gradient_div_sqrt (D : LeviCivitaData g)
    {φ q : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q)
    (hreg : ∀ x ∈ tsupport φ, 0 < q x)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    g.inner x (D.gradient (fun y => φ y / Real.sqrt (q y)) x) v =
      g.inner x (D.gradient φ x) v / Real.sqrt (q x) -
        φ x * g.inner x (D.gradient q x) v / (2 * q x * Real.sqrt (q x)) := by
  by_cases hx : x ∈ tsupport φ
  · have hr := hreg x hx
    have hs := (Real.sqrt_pos.2 hr).ne'
    have hsmooth : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => (Real.sqrt (q y))⁻¹) x :=
      ((Real.contDiffAt_sqrt hr.ne').contMDiffAt.comp x (hq x)).inv₀ hs
    have hd := (Real.hasDerivAt_sqrt hr.ne').inv hs
    have hg := D.gradient_comp ((hq x).mdifferentiableAt (by simp)) hd.differentiableAt
    rw [hd.deriv] at hg
    change D.gradient (fun y => (Real.sqrt (q y))⁻¹) x = _ at hg
    simp only [div_eq_mul_inv]
    rw [D.gradient_mul ((hφ x).mdifferentiableAt (by simp))
      (hsmooth.mdifferentiableAt (by simp))]
    rw [hg]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    have hsq := Real.sq_sqrt hr.le
    field_simp
    rw [hsq]
    ring
  · have hsub : tsupport (fun y => φ y / Real.sqrt (q y)) ⊆ tsupport φ := by
      apply closure_mono
      simp only [Function.support_div]
      exact inter_subset_left
    rw [D.gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)),
      D.gradient_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx]
    simp

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem integral_unitNormal_green (D : LeviCivitaData g)
    {φ f : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hc : HasCompactSupport φ)
    (hreg : ∀ x ∈ tsupport φ, 0 < D.levelQ f x) :
    (∫ x, φ x * D.levelMeanCurvature f x +
      g.inner x (D.gradient φ x) (D.gradient f x) / Real.sqrt (D.levelQ f x)
      ∂g.volumeMeasure) = 0 := by
  let w := fun x => φ x / Real.sqrt (D.levelQ f x)
  have hw := smooth_div_sqrt_on_support hφ (D.contMDiff_levelQ hf) hreg
  have hwc : HasCompactSupport w := by
    simpa only [w, div_eq_mul_inv, Pi.mul_def] using hc.mul_right
  have hi := D.integral_mul_laplacian_of_hasCompactSupport hw hf hwc
  have heq (x : M) :
      φ x * D.levelMeanCurvature f x +
        g.inner x (D.gradient φ x) (D.gradient f x) / Real.sqrt (D.levelQ f x) =
      w x * D.laplacian f x + g.inner x (D.gradient w x) (D.gradient f x) := by
    rw [inner_gradient_div_sqrt D hφ (D.contMDiff_levelQ hf) hreg]
    by_cases hx : x ∈ tsupport φ
    · rw [D.levelMeanCurvature_eq_scalarOperators hf x (hreg x hx)]
      dsimp only [w]
      field_simp
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx, w]
  simp_rw [heq]
  rw [integral_add (D.integrable_mul_laplacian hw hf hwc)
    (D.integrable_inner_gradient hw hf hwc), hi]
  ring

end PoincareConjecture.LeviCivitaData
