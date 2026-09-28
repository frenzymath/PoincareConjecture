import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Localization









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma weighted_bochner_integrand (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (w : M → ℝ) (x : M) :
    w x * ((D.laplacian f x) ^ 2 -
      (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) -
      D.ricci x (D.gradient f x) (D.gradient f x)) =
    w x * (D.laplacian f x) ^ 2 +
      w x * g.inner x (D.gradient (D.laplacian f) x) (D.gradient f x) -
      (1 / 2 : ℝ) * (w x * D.laplacian
        (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x) := by
  have hb := D.bochner_identity hf x
  rw [← D.inner_gradient] at hb
  have h := congrArg (fun z : ℝ => w x * z) hb
  nlinarith only [h]

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]



lemma integrable_weighted_bochner (D : LeviCivitaData g)
    {w f : M → ℝ} (hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hwc : HasCompactSupport w) :
    Integrable (fun x => w x * ((D.laplacian f x) ^ 2 -
      (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) -
      D.ricci x (D.gradient f x) (D.gradient f x))) g.volumeMeasure := by
  simp_rw [weighted_bochner_integrand D hf w]
  apply Integrable.sub
  · apply Integrable.add
    · exact (hw.continuous.mul ((D.contMDiff_laplacian hf).pow 2).continuous).integrable_of_hasCompactSupport
        hwc.mul_right
    · exact (hw.continuous.mul
        (D.continuous_inner_gradient (D.contMDiff_laplacian hf) hf)).integrable_of_hasCompactSupport
        hwc.mul_right
  · exact (D.integrable_mul_laplacian hw (D.contMDiff_inner_gradient hf hf) hwc).const_mul _



theorem integral_weighted_bochner (D : LeviCivitaData g)
    {w f : M → ℝ} (hw : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ w)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hwc : HasCompactSupport w) :
    (∫ x, w x * ((D.laplacian f x) ^ 2 -
      (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) -
      D.ricci x (D.gradient f x) (D.gradient f x)) ∂g.volumeMeasure) =
    ∫ x, (1 / 2 : ℝ) * g.inner x (D.gradient w x)
        (D.gradient (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x) -
      D.laplacian f x * g.inner x (D.gradient w x) (D.gradient f x)
      ∂g.volumeMeasure := by
  let q := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  let A := fun x => w x * (D.laplacian f x) ^ 2
  let B := fun x => w x * g.inner x (D.gradient (D.laplacian f) x) (D.gradient f x)
  let C := fun x => D.laplacian f x * g.inner x (D.gradient w x) (D.gradient f x)
  let Q := fun x => w x * D.laplacian q x
  let E := fun x => g.inner x (D.gradient w x) (D.gradient q x)
  have hl := D.contMDiff_laplacian hf
  have hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q := D.contMDiff_inner_gradient hf hf
  have hA : Integrable A g.volumeMeasure :=
    (hw.continuous.mul (hl.pow 2).continuous).integrable_of_hasCompactSupport hwc.mul_right
  have hB : Integrable B g.volumeMeasure :=
    (hw.continuous.mul (D.continuous_inner_gradient hl hf)).integrable_of_hasCompactSupport
      hwc.mul_right
  have hC : Integrable C g.volumeMeasure :=
    (hl.continuous.mul (D.continuous_inner_gradient hw hf)).integrable_of_hasCompactSupport
      (D.hasCompactSupport_inner_gradient hwc f).mul_left
  have hQ : Integrable Q g.volumeMeasure := D.integrable_mul_laplacian hw hq hwc
  have hE : Integrable E g.volumeMeasure := D.integrable_inner_gradient hw hq hwc
  have hparts : (∫ x, A x ∂g.volumeMeasure) =
      -((∫ x, B x ∂g.volumeMeasure) + ∫ x, C x ∂g.volumeMeasure) := by
    have hp := D.integral_mul_laplacian_of_hasCompactSupport (hw.mul hl) hf hwc.mul_right
    have heq (x : M) :
        g.inner x (D.gradient (fun y => w y * D.laplacian f y) x) (D.gradient f x) =
          B x + C x := by
      rw [D.gradient_mul ((hw x).mdifferentiableAt (by simp))
        ((hl x).mdifferentiableAt (by simp))]
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, B, C]
    simp only [Pi.mul_def, heq] at hp
    rw [integral_add hB hC] at hp
    simpa only [A, pow_two, mul_assoc] using hp
  have hpartsQ : (∫ x, Q x ∂g.volumeMeasure) = -(∫ x, E x ∂g.volumeMeasure) :=
    D.integral_mul_laplacian_of_hasCompactSupport hw hq hwc
  calc
    _ = ∫ x, A x + B x - (1 / 2 : ℝ) * Q x ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (weighted_bochner_integrand D hf w)
    _ = ((∫ x, A x ∂g.volumeMeasure) + ∫ x, B x ∂g.volumeMeasure) -
        (1 / 2 : ℝ) * ∫ x, Q x ∂g.volumeMeasure := by
      have hsub := integral_sub (hA.add hB) (hQ.const_mul (1 / 2 : ℝ))
      simp only [Pi.add_apply] at hsub
      rw [hsub, integral_add hA hB, integral_const_mul]
    _ = (1 / 2 : ℝ) * (∫ x, E x ∂g.volumeMeasure) - ∫ x, C x ∂g.volumeMeasure := by
      rw [hparts, hpartsQ]
      ring
    _ = _ := by
      rw [integral_sub (hE.const_mul _) hC, integral_const_mul]

end PoincareConjecture.LeviCivitaData
