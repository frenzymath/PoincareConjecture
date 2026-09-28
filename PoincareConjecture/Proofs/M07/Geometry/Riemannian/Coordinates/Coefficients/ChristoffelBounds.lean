import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.InverseBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.JetBounds.Operations
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients












noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def koszulOperator :
    (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  let flipT :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toLinearIsometry.toContinuousLinearMap
  let C := ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ)
    (E →L[ℝ] E →L[ℝ] ℝ) flipL
  (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + flipT.comp C - C.comp flipT)

private def christoffelContraction :
    ((E →L[ℝ] ℝ) →L[ℝ] E) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)).comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)

private theorem christoffelBilinear_eq_contraction
    (A : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    CoordinateExponential.christoffelBilinear A x =
      christoffelContraction (A x).inverse (koszulOperator (fderiv ℝ A x)) := by
  rfl

variable [FiniteDimensional ℝ E]



theorem contDiffOn_christoffelBilinear_of_uniformEllipticity
    {ι : Type*} {U : Set E} (hU : IsOpen U)
    {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v) (i : ι) :
    ContDiffOn ℝ ∞ (CoordinateExponential.christoffelBilinear (A i)) U := by
  intro x hx
  exact (CoordinateExponential.contDiffAt_christoffelBilinear
    ((hA i x hx).contDiffAt (hU.mem_nhds hx))
    (isInvertible_of_uniformEllipticity (A := A i x) ha (hell i x hx))).contDiffWithinAt



theorem hasUniformJetBoundsOn_christoffelBilinear
    {ι : Type*} {U : Set E} (hU : IsOpen U)
    {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (hjets : ∀ n, HasUniformJetBoundsOn n U A) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i x, x ∈ U → ∀ v, a * ‖v‖ ^ 2 ≤ A i x v v) (n : ℕ) :
    HasUniformJetBoundsOn n U
      (fun i => CoordinateExponential.christoffelBilinear (A i)) := by
  have hD : ∀ i, ContDiffOn ℝ ∞ (fderiv ℝ (A i)) U :=
    fun i => (hA i).fderiv_of_isOpen hU (by simp)
  have hK : ∀ i, ContDiffOn ℝ ∞
      (fun x => koszulOperator (fderiv ℝ (A i) x)) U :=
    fun i => koszulOperator.contDiff.comp_contDiffOn (hD i)
  have hjK := (hjets (n + 1)).fderiv.clm hU hD koszulOperator
  have hjI := hasUniformJetBoundsOn_inverse_metric hU hA hjets ha hell n
  have hjC := hjI.bilinear hU hjK
    (contDiffOn_inverse_metric hU hA ha hell) hK christoffelContraction
  exact hjC.congr hU fun i x _ =>
    (christoffelBilinear_eq_contraction (A i) x).symm

end PoincareConjecture.CoordinateTransition
