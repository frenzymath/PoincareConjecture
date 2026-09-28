import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Coordinates
import Mathlib.Tactic

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M60

open ConnectionVariation

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covDerivAlong_add (Γ : E → E →L[ℝ] E →L[ℝ] E) (u : P → E)
    {V W : P → E} {p : P} (hV : DifferentiableAt ℝ V p)
    (hW : DifferentiableAt ℝ W p) (d : P) :
    covDerivAlong Γ u (fun x => V x + W x) d p =
      covDerivAlong Γ u V d p + covDerivAlong Γ u W d p := by
  simp only [covDerivAlong, fderiv_fun_add hV hW, add_apply, map_add]
  abel

theorem covDerivAlong_harmonic_trace
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E} {p : P} (d e : P)
    (hu : ContDiffAt ℝ ∞ u p) (hΓ : ContDiffAt ℝ ∞ Γ (u p))
    (hsymm : ∀ᶠ q in 𝓝 p, ∀ a b, Γ (u q) a b = Γ (u q) b a)
    (hharm : ∀ᶠ q in 𝓝 p,
      covDerivAlong Γ u (fun r => fderiv ℝ u r d) d q +
        covDerivAlong Γ u (fun r => fderiv ℝ u r e) e q = 0) :
    covDerivAlong Γ u (covDerivAlong Γ u (fun r => fderiv ℝ u r d) d) d p +
      covDerivAlong Γ u (covDerivAlong Γ u (fun r => fderiv ℝ u r d) e) e p =
      christoffelCurvature Γ (u p) (fderiv ℝ u p e) (fderiv ℝ u p d)
        (fderiv ℝ u p e) := by
  have hu2 : ContDiffAt ℝ 2 u p := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdu (v : P) : ContDiffAt ℝ ∞ (fun r => fderiv ℝ u r v) p :=
    (hu.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hH (v w : P) : ContDiffAt ℝ ∞
      (covDerivAlong Γ u (fun r => fderiv ℝ u r v) w) p :=
    contDiffAt_covDerivAlong hΓ hu (hdu v) w
  have hsum :
      covDerivAlong Γ u (covDerivAlong Γ u (fun r => fderiv ℝ u r d) d) d p +
      covDerivAlong Γ u (covDerivAlong Γ u (fun r => fderiv ℝ u r e) e) d p = 0 := by
    rw [← covDerivAlong_add Γ u ((hH d d).differentiableAt (by simp))
      ((hH e e).differentiableAt (by simp)),
      covDerivAlong_congr Γ u hharm, covDerivAlong_zero]
  have hswap : covDerivAlong Γ u (fun r => fderiv ℝ u r d) e =ᶠ[𝓝 p]
      covDerivAlong Γ u (fun r => fderiv ℝ u r e) d := by
    filter_upwards [hu2.eventually (by norm_num), hsymm] with q hq hsq
    exact covDerivAlong_fderiv_symm hq hsq e d
  have hcomm := covDerivAlong_comm hu2 ((hdu e).of_le (WithTop.coe_le_coe.mpr le_top))
    (hΓ.differentiableAt (by simp)) e d
  rw [covDerivAlong_congr Γ u hswap e]
  rw [eq_neg_of_add_eq_zero_left hsum]
  simpa only [sub_eq_add_neg, add_comm] using hcomm

end PoincareConjecture.M60
