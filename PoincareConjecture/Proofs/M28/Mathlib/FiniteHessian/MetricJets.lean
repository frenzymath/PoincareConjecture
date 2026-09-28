import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.JetBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.InverseBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.Proofs.M28.FiniteHessian

section Derivative

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem HasUniformJetBoundsAt.fderiv {n : ℕ} {f : ι → E → F} {x : ι → E}
    (h : HasUniformJetBoundsAt (n + 1) f x) :
    HasUniformJetBoundsAt n (fun i => fderiv ℝ (f i)) x := by
  intro m hm
  obtain ⟨C, hC⟩ := h (m + 1) (by omega)
  exact ⟨C, fun i => by simpa only [norm_iteratedFDeriv_fderiv] using hC i⟩

end Derivative

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem HasUniformJetBoundsAt.inverse_metric {n : ℕ}
    {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {x : ι → E}
    (hjets : HasUniformJetBoundsAt (n + 1) A x)
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i v, a * ‖v‖ ^ 2 ≤ A i (x i) v v) :
    HasUniformJetBoundsAt n (fun i y => (A i y).inverse) x := by
  obtain ⟨C, hC⟩ := hjets 0 (Nat.zero_le _)
  have houter : HasUniformJetBoundsAt n
      (fun _ : ι => ContinuousLinearMap.inverse :
        ι → (E →L[ℝ] E →L[ℝ] ℝ) → (E →L[ℝ] ℝ) →L[ℝ] E)
      (fun i => A i (x i)) := by
    intro m hm
    obtain ⟨B, hB⟩ :=
      CoordinateTransition.hasUniformJetBoundsOn_inverse_elliptic (E := E) ha C n m hm
    refine ⟨B, fun i => hB () (A i (x i)) ⟨?_, hell i⟩⟩
    simpa only [norm_iteratedFDeriv_zero] using hC i
  exact hjets.fderiv.comp_of_fderiv houter hA (fun i =>
    (CoordinateTransition.isInvertible_of_uniformEllipticity ha (hell i)).contDiffAt_map_inverse)




theorem hasUniformJetBoundsAt_christoffelBilinear {n : ℕ}
    {A : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {x : ι → E}
    (hjets : HasUniformJetBoundsAt (n + 1) A x)
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (x i)) {a : ℝ} (ha : 0 < a)
    (hell : ∀ i v, a * ‖v‖ ^ 2 ≤ A i (x i) v v) :
    HasUniformJetBoundsAt n
      (fun i => CoordinateExponential.christoffelBilinear (A i)) x := by
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap
  let flipT :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toLinearIsometry.toContinuousLinearMap
  let C := ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ)
    (E →L[ℝ] E →L[ℝ] ℝ) flipL
  let K : (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ]
      E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    (2⁻¹ : ℝ) • (ContinuousLinearMap.id ℝ _ + flipT.comp C - C.comp flipT)
  let contract : ((E →L[ℝ] ℝ) →L[ℝ] E) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E)).comp
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E)
  have hD : ∀ i, ContDiffAt ℝ ∞ (fderiv ℝ (A i)) (x i) :=
    fun i => (hA i).fderiv_right (by simp)
  have hK : ∀ i, ContDiffAt ℝ ∞ (fun y => K (fderiv ℝ (A i) y)) (x i) :=
    fun i => K.contDiff.contDiffAt.comp (x i) (hD i)
  have hI : ∀ i, ContDiffAt ℝ ∞ (fun y => (A i y).inverse) (x i) :=
    fun i => (CoordinateTransition.isInvertible_of_uniformEllipticity ha
      (hell i)).contDiffAt_map_inverse.comp (x i) (hA i)
  have hjK := hjets.fderiv.clm hD K
  have hjI := hjets.inverse_metric hA ha hell
  apply (hjI.bilinear hjK hI hK contract).congr_germ
  intro i
  exact Filter.Eventually.of_forall (fun _ => rfl)

end PoincareConjecture.Proofs.M28.FiniteHessian
