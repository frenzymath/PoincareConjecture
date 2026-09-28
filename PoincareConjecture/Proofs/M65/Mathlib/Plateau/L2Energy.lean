import PoincareConjecture.Proofs.M65.Mathlib.Plateau.WeakEnergy
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients











set_option autoImplicit false

open Filter
open scoped Topology InnerProductSpace

namespace MeasureTheory.Lp

variable {X E F : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]




theorem coefficientL2_adjoint [CompleteSpace E] [CompleteSpace F] (A : X → E →L[ℝ] F)
    (hA : AEStronglyMeasurable A mu) (C : ℝ)
    (hbound : ∀ᵐ x ∂mu, ‖A x‖ ≤ C)
    (hstar : AEStronglyMeasurable (fun x => (A x).adjoint) mu)
    (hstarbound : ∀ᵐ x ∂mu, ‖(A x).adjoint‖ ≤ C) :
    (coefficientL2 A hA C hbound).adjoint =
      coefficientL2 (fun x => (A x).adjoint) hstar C hstarbound := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientL2_ae A hA C hbound u,
    coefficientL2_ae (fun x => (A x).adjoint) hstar C hstarbound v] with x hx hxstar
  rw [hx, hxstar, ContinuousLinearMap.adjoint_inner_left]




theorem norm_sq_coefficientL2 (A : X → E →L[ℝ] F)
    (hA : AEStronglyMeasurable A mu) (C : ℝ)
    (hbound : ∀ᵐ x ∂mu, ‖A x‖ ≤ C) (u : Lp E 2 mu) :
    ‖coefficientL2 A hA C hbound u‖ ^ 2 = ∫ x, ‖A x (u x)‖ ^ 2 ∂mu := by
  rw [norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [coefficientL2_ae A hA C hbound u] with x hx
  rw [hx]





theorem integral_norm_sq_clm_le_of_weak [CompleteSpace E] [CompleteSpace F]
    {A : ℕ → X → E →L[ℝ] F} {A0 : X → E →L[ℝ] F}
    (hA : ∀ n, AEStronglyMeasurable (A n) mu)
    (hA0 : AEStronglyMeasurable A0 mu) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ∀ᵐ x ∂mu, ‖A n x‖ ≤ C)
    (hbound0 : ∀ᵐ x ∂mu, ‖A0 x‖ ≤ C)
    (hconv : ∀ᵐ x ∂mu, Tendsto (fun n => A n x) atTop (𝓝 (A0 x)))
    {u : ℕ → Lp E 2 mu} {u0 : Lp E 2 mu} {B energy : ℝ}
    (hubound : ∀ᶠ n in atTop, ‖u n‖ ≤ B)
    (huweak : ∀ v : Lp E 2 mu,
      Tendsto (fun n => ⟪u n, v⟫_ℝ) atTop (𝓝 ⟪u0, v⟫_ℝ))
    (henergy : Tendsto (fun n => ∫ x, ‖A n x (u n x)‖ ^ 2 ∂mu) atTop (𝓝 energy)) :
    (∫ x, ‖A0 x (u0 x)‖ ^ 2 ∂mu) ≤ energy := by
  have hstar (n : ℕ) : AEStronglyMeasurable (fun x => (A n x).adjoint) mu :=
    ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable (hA n)
  have hstar0 : AEStronglyMeasurable (fun x => (A0 x).adjoint) mu :=
    ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable hA0
  have hstarbound (n : ℕ) : ∀ᵐ x ∂mu, ‖(A n x).adjoint‖ ≤ C := by
    simpa only [LinearIsometryEquiv.norm_map] using hbound n
  have hstarbound0 : ∀ᵐ x ∂mu, ‖(A0 x).adjoint‖ ≤ C := by
    simpa only [LinearIsometryEquiv.norm_map] using hbound0
  have hstarconv : ∀ᵐ x ∂mu,
      Tendsto (fun n => (A n x).adjoint) atTop (𝓝 (A0 x).adjoint) := by
    filter_upwards [hconv] with x hx
    exact ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp hx
  have hstrong (v : Lp F 2 mu) :
      Tendsto (fun n => (coefficientL2 (A n) (hA n) C (hbound n)).adjoint v) atTop
        (𝓝 ((coefficientL2 A0 hA0 C hbound0).adjoint v)) := by
    simp only [coefficientL2_adjoint (A _) (hA _) C (hbound _) (hstar _) (hstarbound _),
      coefficientL2_adjoint A0 hA0 C hbound0 hstar0 hstarbound0]
    exact tendsto_coefficientL2_apply hstar hstar0 hC hstarbound hstarbound0 hstarconv v
  have henergy' :
      Tendsto (fun n => ‖coefficientL2 (A n) (hA n) C (hbound n) (u n)‖ ^ 2)
        atTop (𝓝 energy) := by
    simpa only [norm_sq_coefficientL2] using henergy
  have hle := InnerProductSpace.norm_sq_apply_le_of_adjoint_tendsto
    hubound huweak hstrong henergy'
  simpa only [norm_sq_coefficientL2] using hle

end MeasureTheory.Lp
