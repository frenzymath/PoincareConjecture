import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.BundleContact

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M60

open Poincare.Riemannian.RadialTransport

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem second_fderiv_metric_pairing
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {Y Z : E → F} {O : Set E} {p : E}
    (hO : IsOpen O) (hp : p ∈ O)
    (hΓ : ContDiffOn ℝ ∞ Γ O) (hG : ContDiffOn ℝ ∞ G O)
    (hY : ContDiffOn ℝ ∞ Y O) (hZ : ContDiffOn ℝ ∞ Z O)
    (hcompat : ∀ x ∈ O, ∀ u : E, ∀ a b : F,
      fderiv ℝ (fun z => G z a b) x u =
        G x (Γ x u a) b + G x a (Γ x u b)) (u v : E) :
    fderiv ℝ (fun x => fderiv ℝ (fun z => G z (Y z) (Z z)) x u) p v =
      G p (covariantDerivative Γ (fun x => covariantDerivative Γ Y x u) p v) (Z p) +
      G p (covariantDerivative Γ Y p u) (covariantDerivative Γ Z p v) +
      G p (covariantDerivative Γ Y p v) (covariantDerivative Γ Z p u) +
      G p (Y p) (covariantDerivative Γ (fun x => covariantDerivative Γ Z x u) p v) := by
  have hΓp := hΓ.contDiffAt (hO.mem_nhds hp)
  have hGp := hG.contDiffAt (hO.mem_nhds hp)
  have hYp := hY.contDiffAt (hO.mem_nhds hp)
  have hZp := hZ.contDiffAt (hO.mem_nhds hp)
  have hDY := contDiffAt_covariantDerivative hΓp hYp u
  have hDZ := contDiffAt_covariantDerivative hΓp hZp u
  have heq : (fun x => fderiv ℝ (fun z => G z (Y z) (Z z)) x u) =ᶠ[𝓝 p]
      (fun x => G x (covariantDerivative Γ Y x u) (Z x) +
        G x (Y x) (covariantDerivative Γ Z x u)) := by
    filter_upwards [hO.mem_nhds hp] with x hx
    exact fderiv_metric_pairing
      ((hG.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      ((hY.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      ((hZ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))
      (hcompat x hx) u
  rw [heq.fderiv_eq, fderiv_fun_add
    (((hGp.clm_apply hDY).clm_apply hZp).differentiableAt (by simp))
    (((hGp.clm_apply hYp).clm_apply hDZ).differentiableAt (by simp))]
  simp only [add_apply]
  rw [fderiv_metric_pairing (hGp.differentiableAt (by simp))
    (hDY.differentiableAt (by simp)) (hZp.differentiableAt (by simp)) (hcompat p hp),
    fderiv_metric_pairing (hGp.differentiableAt (by simp))
      (hYp.differentiableAt (by simp)) (hDZ.differentiableAt (by simp)) (hcompat p hp)]
  ring

theorem second_fderiv_metric_self
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {Y : E → F} {O : Set E} {p : E}
    (hO : IsOpen O) (hp : p ∈ O)
    (hΓ : ContDiffOn ℝ ∞ Γ O) (hG : ContDiffOn ℝ ∞ G O)
    (hY : ContDiffOn ℝ ∞ Y O)
    (hcompat : ∀ x ∈ O, ∀ u : E, ∀ a b : F,
      fderiv ℝ (fun z => G z a b) x u =
        G x (Γ x u a) b + G x a (Γ x u b))
    (hsymm : ∀ a b : F, G p a b = G p b a) (u : E) :
    fderiv ℝ (fun x => fderiv ℝ (fun z => G z (Y z) (Y z)) x u) p u =
      2 * G p (covariantDerivative Γ (fun x => covariantDerivative Γ Y x u) p u)
        (Y p) + 2 * G p (covariantDerivative Γ Y p u) (covariantDerivative Γ Y p u) := by
  rw [second_fderiv_metric_pairing hO hp hΓ hG hY hY hcompat]
  rw [hsymm (Y p)]
  ring

end PoincareConjecture.M60
