import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Forcing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.HolderProduct

noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff NNReal Topology

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}

theorem holderWith_half_of_norm_fderiv_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : Differentiable ℝ f) {M L : ℝ≥0}
    (hM : ∀ x, ‖f x‖ ≤ M) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L) :
    HolderWith (max (2 * M) L) (1 / 2) f := by
  have hlip : LipschitzWith L f := lipschitzWith_of_nnnorm_fderiv_le hf (fun x => by
    exact_mod_cast hL x)
  exact (Poincare.Parabolic.Interior.holderWith_zero_of_norm_le hM).of_le_of_le
    hlip.holderWith (by positivity) (by norm_num)

theorem holderWith_euclidean_gradient {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {H α : ℝ≥0} (hu : HolderWith H α (fderiv ℝ u)) :
    HolderWith H α (_root_.gradient u) := by
  have h := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.lipschitz.holderWith.comp hu
  have hC : (1 * H ^ ((1 : ℝ≥0) : ℝ)) = H := by simp
  have hα : (1 * α : ℝ≥0) = α := by simp
  rw [hC, hα] at h
  have hgrad : _root_.gradient u =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ∘ fderiv ℝ u := by
    funext x
    rfl
  simpa only [hgrad] using h

def coordinateErrorFlux
    (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (E x (_root_.gradient u x)) i

theorem contDiff_coordinateErrorFlux
    {E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hE : ContDiff ℝ ∞ E)
    (hu : ContDiff ℝ ∞ u) (i : Fin n) :
    ContDiff ℝ ∞ (coordinateErrorFlux E u i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
    (hE.clm_apply (contDiff_euclidean_gradient hu))

theorem hasCompactSupport_coordinateErrorFlux
    (E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : HasCompactSupport u) (i : Fin n) :
    HasCompactSupport (coordinateErrorFlux E u i) := by
  apply (hu.fderiv ℝ).mono
  intro x hx
  by_contra hd
  have hd' : fderiv ℝ u x = 0 := Function.notMem_support.mp hd
  exact hx (by simp [coordinateErrorFlux, gradient, hd'])

theorem holderWith_coordinateErrorFlux
    {E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {ε L H M : ℝ≥0}
    (hE : HolderWith L (1 / 2) E) (hu : HolderWith H (1 / 2) (fderiv ℝ u))
    (hEbound : ∀ x, ‖E x‖ ≤ ε) (hubound : ∀ x, ‖fderiv ℝ u x‖ ≤ M) (i : Fin n) :
    HolderWith (ε * H + L * M) (1 / 2) (coordinateErrorFlux E u i) := by
  have hgrad := holderWith_euclidean_gradient hu
  have hflux := Poincare.Parabolic.Interior.holderWith_clm_apply hE hgrad hEbound
    (fun x => (norm_euclidean_gradient_eq u x).trans_le (hubound x))
  have hproj : LipschitzWith 1 (fun v : EuclideanSpace ℝ (Fin n) => v i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, PiLp.sub_apply, NNReal.coe_one, one_mul] using
      PiLp.norm_apply_le (x - y) i
  have hcomp := hproj.holderWith.comp hflux
  have hC : (1 * (ε * H + L * M) ^ ((1 : ℝ≥0) : ℝ)) = ε * H + L * M := by simp
  have hα : (1 * (1 / 2 : ℝ≥0)) = 1 / 2 := by simp
  rw [hC, hα] at hcomp
  have hflux : coordinateErrorFlux E u i =
      (fun v : EuclideanSpace ℝ (Fin n) => v i) ∘
        (fun x => E x (_root_.gradient u x)) := by
    funext x
    rfl
  simpa only [hflux] using hcomp

end PoincareConjecture.HarmonicCoordinates
