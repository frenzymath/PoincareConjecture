import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerDyadicHolder
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped ContDiff Topology Convolution

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem suWeakPartial_kernel_identity {O : Set Plane} (hO : MeasurableSet O)
    {u p : Plane → ℝ} {i : Fin 2} (hw : HasWeakPartialDeriv i p u O)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : Plane) (hs : tsupport (fun y => φ (x - y)) ⊆ O) :
    ((fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) ⋆[lsmul ℝ ℝ, volume]
      O.indicator u) x = (φ ⋆[lsmul ℝ ℝ, volume] O.indicator p) x := by
  classical
  let ψ : Plane → ℝ := fun y => φ (x - y)
  let T : Plane ≃ₜ Plane := (Homeomorph.neg Plane).trans (Homeomorph.addLeft x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := by
    simpa [ψ, T, Function.comp_def, sub_eq_add_neg] using hc.comp_homeomorph T
  have hd (y : Plane) : fderiv ℝ ψ y (EuclideanSpace.single i 1) =
      -fderiv ℝ φ (x - y) (EuclideanSpace.single i 1) := by
    have h := (hφ.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt ψ _ y at h
    rw [h.fderiv]
    simp
  have ht := hw ψ hψ hψc hs
  simp_rw [hd, mul_neg] at ht
  rw [integral_neg] at ht
  have heq := neg_injective ht
  have hind (v k : Plane → ℝ) :
      (∫ y, k y * O.indicator v y) = ∫ y in O, k y * v y := by
    rw [← integral_indicator hO]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by by_cases hy : y ∈ O <;> simp [hy]
  rw [convolution_lsmul_swap, convolution_lsmul_swap]
  simp only [smul_eq_mul]
  rw [hind, hind]
  simpa only [ψ, mul_comm] using heq

theorem suConvolution_map {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : Plane → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {u : Plane → E} (hu : LocallyIntegrable u volume) (B : E →L[ℝ] F) (x : Plane) :
    B ((φ ⋆[lsmul ℝ ℝ, volume] u) x) =
      (φ ⋆[lsmul ℝ ℝ, volume] (B ∘ u)) x := by
  have hi := (hc.convolutionExists_left (lsmul ℝ ℝ) hφ hu x).integrable
  change Integrable (fun t => φ t • u (x - t)) volume at hi
  change B (∫ t, φ t • u (x - t)) = ∫ t, φ t • B (u (x - t))
  rw [← B.integral_comp_comm hi]
  simp only [map_smul]

theorem suConvolution_fderiv_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {u : Plane → E} (hu : LocallyIntegrable u volume) (x e : Plane) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] u) x e =
      ((fun y => fderiv ℝ φ y e) ⋆[lsmul ℝ ℝ, volume] u) x := by
  have hd := hc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) (hφ.of_le (by simp)) hu x
  rw [hd.fderiv]
  have hi := ((hc.fderiv ℝ).convolutionExists_left ((lsmul ℝ ℝ).precompL Plane)
    (hφ.continuous_fderiv (by simp)) hu x).integrable
  change (∫ t, ((lsmul ℝ ℝ).precompL Plane) (fderiv ℝ φ t) (u (x - t))) e = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem suWeak_convolution_fderiv {m : ℕ} {O : Set Plane} (hO : MeasurableSet O)
    {u p : Plane → EuclideanSpace ℝ (Fin m)} {i : Fin 2}
    (hw : ∀ b, HasWeakPartialDeriv i (fun y => p y b) (fun y => u y b) O)
    (hu : LocallyIntegrable (O.indicator u) volume)
    (hp : LocallyIntegrable (O.indicator p) volume)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : Plane) (hs : tsupport (fun y => φ (x - y)) ⊆ O) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, volume] O.indicator u) x (EuclideanSpace.single i 1) =
      (φ ⋆[lsmul ℝ ℝ, volume] O.indicator p) x := by
  classical
  rw [suConvolution_fderiv_apply hφ hc hu]
  ext b
  let B : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := EuclideanSpace.proj b
  change B (_) = B (_)
  rw [suConvolution_map ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ _) hu B,
    suConvolution_map hφ.continuous hc hp B]
  have hid (v : Plane → EuclideanSpace ℝ (Fin m)) :
      B ∘ O.indicator v = O.indicator (fun y => v y b) := by
    ext y
    by_cases hy : y ∈ O <;> simp [B, hy]
  rw [hid, hid]
  exact suWeakPartial_kernel_identity hO (hw b) hφ hc x hs

end PoincareConjecture.M60

end
