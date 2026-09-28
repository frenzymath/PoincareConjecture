import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelBounds

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem hasUniformJetBoundsOn_inverse_metric_finite
    {ι : Type*} {n : ℕ} {U : Set E} (hU : IsOpen U)
    {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ i, ContDiffOn ℝ n (A i) U)
    (hjets : HasUniformJetBoundsOn n U A) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v) :
    HasUniformJetBoundsOn n U (fun i x => (A i x).inverse) := by
  obtain ⟨C, hC⟩ := hjets 0 (Nat.zero_le n)
  let K := {B : E →L[ℝ] E →L[ℝ] ℝ | ‖B‖ ≤ C ∧ ∀ v, a * ‖v‖ ^ 2 ≤ B v v}
  have hK : IsCompact K := isCompact_bounded_uniformlyElliptic a C
  apply hjets.comp_fixed_at hU hK hA
    (fun B hB => (isInvertible_of_uniformEllipticity ha hB.2).contDiffAt_map_inverse)
  intro i x hx
  exact ⟨by simpa only [norm_iteratedFDeriv_zero] using hC i x hx, hell i x hx⟩

private noncomputable def capKoszulOperator :
    (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  let flipT :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toLinearIsometry.toContinuousLinearMap
  let C := ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ)
    (E →L[ℝ] E →L[ℝ] ℝ) flipL
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + flipT.comp C - C.comp flipT)

private noncomputable def capChristoffelContraction :
    ((E →L[ℝ] ℝ) →L[ℝ] E) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)).comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)

theorem hasUniformJetBoundsOn_christoffelBilinear_finite
    {ι : Type*} {n : ℕ} {U : Set E} (hU : IsOpen U)
    {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hjets : HasUniformJetBoundsOn (n + 1) U A) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v) :
    HasUniformJetBoundsOn n U
      (fun i => CoordinateExponential.christoffelBilinear (A i)) := by
  have hD : ∀ i, ContDiffOn ℝ ∞ (fderiv ℝ (A i)) U :=
    fun i => (hA i).fderiv_of_isOpen hU (by simp)
  have hK : ∀ i, ContDiffOn ℝ ∞
      (fun x => capKoszulOperator (fderiv ℝ (A i) x)) U :=
    fun i => capKoszulOperator.contDiff.comp_contDiffOn (hD i)
  have hjK := hjets.fderiv.clm hU hD capKoszulOperator
  have hjI := hasUniformJetBoundsOn_inverse_metric_finite hU
    (fun i => (hA i).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
    (hjets.mono_order (Nat.le_succ n)) ha hell
  have hjC := hjI.bilinear hU hjK
    (contDiffOn_inverse_metric hU hA ha hell) hK capChristoffelContraction
  exact hjC.congr hU fun _ _ _ => rfl

end PoincareConjecture.CoordinateTransition
