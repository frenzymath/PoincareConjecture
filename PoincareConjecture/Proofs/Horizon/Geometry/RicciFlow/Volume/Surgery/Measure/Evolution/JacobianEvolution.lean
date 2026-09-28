import PoincareConjecture.Proofs.M10.JacobianEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Analysis.DeterminantCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul






















set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace PoincareConjecture.SurgeryVolume.Measure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]








theorem hasDerivAt_jacobian_of_normalized_gram
    {J : ℝ → ℝ} {A : ℝ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ} {t : ℝ}
    (hJ : J =ᶠ[𝓝 t] (fun s ↦ Real.sqrt ((A s).det)))
    (hA : HasDerivAt A B t) (hAt : A t = 1) :
    HasDerivAt J (B.trace / 2) t := by
  exact (hasDerivAt_sqrt_matrix_det_of_eq_one hA hAt).congr_of_eventuallyEq hJ


theorem hasDerivAt_jacobian_of_scaled_normalized_gram
    {J : ℝ → ℝ} {A : ℝ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ} {t c : ℝ}
    (hc : c ≠ 0)
    (hJ : (fun s ↦ c * J s) =ᶠ[𝓝 t] (fun s ↦ Real.sqrt ((A s).det)))
    (hA : HasDerivAt A B t) (hAt : A t = 1) :
    HasDerivAt J (J t * (B.trace / 2)) t := by
  have hnorm : c * J t = 1 := by
    simpa only [hAt, Matrix.det_one, Real.sqrt_one] using hJ.eq_of_nhds
  have h := (hasDerivAt_jacobian_of_normalized_gram hJ hA hAt).const_mul c⁻¹
  have hfun : (fun s ↦ c⁻¹ * (c * J s)) = J := by
    funext s
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [hfun] at h
  have hvalue : c⁻¹ = J t := by
    calc
      c⁻¹ = c⁻¹ * (c * J t) := by rw [hnorm, mul_one]
      _ = J t := by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  simpa only [hvalue] using h

end PoincareConjecture.SurgeryVolume.Measure
