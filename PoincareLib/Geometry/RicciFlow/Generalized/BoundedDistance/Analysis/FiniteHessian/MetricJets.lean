import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.FiniteHessian.JetBounds
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients.InverseBounds
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients

/-!
# Finite pointwise metric and connection jets

Finite coefficient jets and ellipticity at the tested points suffice for
finite inverse and Christoffel jets. There is no all-orders assumption or
common domain for the germs. Source: Morgan--Tian Proposition 9.79,
pp. 232-234, and Proposition 10.7, p. 253; M28 derivation 100.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT.Proofs.M28.FiniteHessian

section Derivative

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- One fewer order bounds the derivative family at the same points.
Source: the finite coefficient budget in M28 derivation 100. -/
theorem HasUniformJetBoundsAt.fderiv {n : ℕ} {f : ι → E → F} {x : ι → E}
    (h : HasUniformJetBoundsAt (n + 1) f x) :
    HasUniformJetBoundsAt n (fun i => fderiv ℝ (f i)) x := by
  intro m hm
  obtain ⟨C, hC⟩ := h (m + 1) (by omega)
  exact ⟨C, fun i => by simpa only [norm_iteratedFDeriv_fderiv] using hC i⟩

end Derivative

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite coefficient budget bounds inverse jets at uniformly elliptic
tested points. The extra derivative is also needed for the connection.
Source: M28 derivation 100, finite composition with actual inversion. -/
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

/-- The actual coordinate connection has one fewer bounded jet than the
metric coefficients, with ellipticity needed only at the tested points.
Source: the finite Koszul contraction in M28 derivation 100. -/
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

end PoincareMT.Proofs.M28.FiniteHessian
