import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Jacobi.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set

namespace Poincare.ODE.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isJacobiSolOn_spherical (A : E →L[ℝ] E) {c : ℝ} (hc : c ≠ 0)
    (w₀ w₁ : E) (h₀ : A w₀ = 0) (h₁ : A w₁ = c ^ 2 • w₁) (a b : ℝ) :
    IsJacobiSolOn (fun _ => A) a b
      (fun t => t • w₀ + (Real.sin (c * t) / c) • w₁)
      (fun t => w₀ + Real.cos (c * t) • w₁) := by
  constructor
  · intro t _
    have hs := ((Real.hasDerivAt_sin (c * t)).comp t
      ((hasDerivAt_id t).const_mul c)).div_const c
    have hs' : HasDerivAt (fun s => Real.sin (c * s) / c)
        (Real.cos (c * t)) t := by
      simpa [hc] using hs
    simpa only [Pi.add_def, id_eq, one_smul] using (((hasDerivAt_id t).smul_const w₀).add
      (hs'.smul_const w₁)).hasDerivWithinAt
  · intro t _
    have hs := ((Real.hasDerivAt_cos (c * t)).comp t
      ((hasDerivAt_id t).const_mul c)).smul_const w₁
    have heq : -(Real.sin (c * t) / c * c ^ 2) = -Real.sin (c * t) * (c * 1) := by
      field_simp
    simpa only [Pi.add_def, Function.comp_def, map_add, map_smul, h₀, h₁, smul_zero, zero_add,
      smul_smul, ← neg_smul, heq] using
      ((hasDerivAt_const t w₀).add hs).hasDerivWithinAt


theorem IsJacobiSolOn.eq_spherical
    {A : E →L[ℝ] E} {c b : ℝ} (hc : c ≠ 0)
    {w₀ w₁ : E} (h₀ : A w₀ = 0) (h₁ : A w₁ = c ^ 2 • w₁)
    {y v : ℝ → E} (h : IsJacobiSolOn (fun _ => A) 0 b y v)
    (hy : y 0 = 0) (hv : v 0 = w₀ + w₁) {t : ℝ} (ht : t ∈ Icc 0 b) :
    y t = t • w₀ + (Real.sin (c * t) / c) • w₁ ∧
      v t = w₀ + Real.cos (c * t) • w₁ := by
  have hmodel := isJacobiSolOn_spherical A hc w₀ w₁ h₀ h₁ 0 b
  have heq := h.isSolOn_pair.eqOn_of_left
    (K := ‖pairCoeff (fun _ => A) 0‖₊) (fun _ _ => le_rfl)
    hmodel.isSolOn_pair (by simp [hy, hv]) ht
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

end Poincare.ODE.Jacobi
