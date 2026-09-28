import PoincareConjecture.Proofs.M60.Mathlib.CovariantPairing
import PoincareConjecture.Proofs.M60.Mathlib.PositiveBilinearPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M60

open Poincare.Riemannian.RadialTransport

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conformal_pairing_derivatives
    {Γ : P → P →L[ℝ] E →L[ℝ] E} {G : P → E →L[ℝ] E →L[ℝ] ℝ}
    {Y Z : P → E} {a : P → ℝ} {p : P} (d e : P)
    (hG : DifferentiableAt ℝ G p) (hY : DifferentiableAt ℝ Y p)
    (hZ : DifferentiableAt ℝ Z p)
    (hcompat : ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun q => G q b c) p v =
        G p (Γ p v b) c + G p b (Γ p v c))
    (hsymm : ∀ b c : E, G p b c = G p c b)
    (hYY : (fun q => G q (Y q) (Y q)) =ᶠ[𝓝 p] a)
    (hZZ : (fun q => G q (Z q) (Z q)) =ᶠ[𝓝 p] a)
    (hYZ : (fun q => G q (Y q) (Z q)) =ᶠ[𝓝 p] (fun _ => 0))
    (htor : covariantDerivative Γ Z p d = covariantDerivative Γ Y p e) :
    G p (covariantDerivative Γ Y p d) (Y p) = fderiv ℝ a p d / 2 ∧
    G p (covariantDerivative Γ Y p d) (Z p) = -fderiv ℝ a p e / 2 ∧
    G p (covariantDerivative Γ Y p e) (Y p) = fderiv ℝ a p e / 2 ∧
    G p (covariantDerivative Γ Y p e) (Z p) = fderiv ℝ a p d / 2 := by
  have h1 := fderiv_metric_pairing hG hY hY hcompat d
  have h2 := fderiv_metric_pairing hG hY hY hcompat e
  have h3 := fderiv_metric_pairing hG hZ hZ hcompat d
  have h4 := fderiv_metric_pairing hG hY hZ hcompat d
  rw [hYY.fderiv_eq, hsymm (Y p)] at h1 h2
  rw [hZZ.fderiv_eq, htor, hsymm (Z p)] at h3
  rw [hYZ.fderiv_eq, fderiv_const_apply, zero_apply,
    htor, hsymm (Y p)] at h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem conformal_pairing_gradient_bound
    {Γ : P → P →L[ℝ] E →L[ℝ] E} {G : P → E →L[ℝ] E →L[ℝ] ℝ}
    {Y Z : P → E} {a : P → ℝ} {p : P} (d e : P)
    (hG : DifferentiableAt ℝ G p) (hY : DifferentiableAt ℝ Y p)
    (hZ : DifferentiableAt ℝ Z p)
    (hcompat : ∀ v : P, ∀ b c : E,
      fderiv ℝ (fun q => G q b c) p v =
        G p (Γ p v b) c + G p b (Γ p v c))
    (hsymm : ∀ b c : E, G p b c = G p c b) (hnonneg : ∀ w, 0 ≤ G p w w)
    (hYY : (fun q => G q (Y q) (Y q)) =ᶠ[𝓝 p] a)
    (hZZ : (fun q => G q (Z q) (Z q)) =ᶠ[𝓝 p] a)
    (hYZ : (fun q => G q (Y q) (Z q)) =ᶠ[𝓝 p] (fun _ => 0))
    (htor : covariantDerivative Γ Z p d = covariantDerivative Γ Y p e)
    (ha : 0 < a p) :
    ((fderiv ℝ a p d) ^ 2 + (fderiv ℝ a p e) ^ 2) / a p ≤
      2 * (G p (covariantDerivative Γ Y p d) (covariantDerivative Γ Y p d) +
        G p (covariantDerivative Γ Y p e) (covariantDerivative Γ Y p e)) := by
  obtain ⟨hAu, hAv, hBu, hBv⟩ :=
    conformal_pairing_derivatives d e hG hY hZ hcompat hsymm hYY hZZ hYZ htor
  exact conformal_bilinear_hessian_bound (G p) hsymm hnonneg
    (Y p) (Z p) _ _ ha hYY.eq_of_nhds hZZ.eq_of_nhds hYZ.eq_of_nhds hAu hAv hBu hBv

end PoincareConjecture.M60
