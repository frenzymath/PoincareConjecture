import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic









set_option autoImplicit false

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def continuousTrace : (E →L[ℝ] E) →L[ℝ] ℝ :=
  ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

theorem continuousTrace_apply (A : E →L[ℝ] E) :
    continuousTrace A = LinearMap.trace ℝ E A.toLinearMap := rfl

theorem continuousTrace_mul_comm (A B : E →L[ℝ] E) :
    continuousTrace (A * B) = continuousTrace (B * A) :=
  LinearMap.trace_mul_comm ℝ A.toLinearMap B.toLinearMap

theorem inverseMetricTrace_hasDerivAt
    (A B : ℝ → E →L[ℝ] E) (A' B' : E →L[ℝ] E) (t : ℝ)
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t)
    (hunit : IsUnit (A t)) (P Q C : E →L[ℝ] E)
    (hA' : A' = A t * P + Q * A t)
    (hB' : B' = B t * P + Q * B t + C) :
    HasDerivAt (fun s ↦ continuousTrace (Ring.inverse (A s) * B s))
      (continuousTrace (Ring.inverse (A t) * C)) t := by
  obtain ⟨u, hu⟩ := hunit
  have hinv : HasDerivAt (fun s ↦ Ring.inverse (A s))
      (-((↑u⁻¹ : E →L[ℝ] E) * A' * ↑u⁻¹)) t := by
    have hout := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at hout
    have h := hout.comp_hasDerivAt t hA
    convert! h using 1
  have h := (continuousTrace (E := E)).hasFDerivAt.comp_hasDerivAt t (hinv.mul hB)
  have hinvt : Ring.inverse (A t) = (↑u⁻¹ : E →L[ℝ] E) := by
    rw [← hu, Ring.inverse_unit]
  have halgebra : -((↑u⁻¹ : E →L[ℝ] E) * A' * ↑u⁻¹) * B t +
      Ring.inverse (A t) * B' =
      ↑u⁻¹ * C + (↑u⁻¹ * B t) * P - P * (↑u⁻¹ * B t) := by
    rw [hA', hB', hinvt, ← hu]
    noncomm_ring [u.inv_mul, u.mul_inv]
    simp only [← mul_assoc, u.inv_mul, one_mul]
    module
  apply h.congr_deriv
  rw [halgebra, map_sub, map_add, continuousTrace_mul_comm P, add_sub_cancel_right, hinvt]

end PoincareConjecture.Proofs.M09
