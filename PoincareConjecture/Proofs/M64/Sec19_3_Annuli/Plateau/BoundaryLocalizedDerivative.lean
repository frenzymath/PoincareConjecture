import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularSlice
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64LocalizedSource_horizontal_derivative
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    {eta rho : ℝ → ℝ} (heta : Differentiable ℝ eta) {t : ℝ}
    (hvar : ∀ x s, T (annulusPoint x s) = annulusPoint (x + t * eta x * rho s) s)
    (p : LoopPlane) :
    fderiv ℝ T p e0 0 = 1 + t * deriv eta (p 0) * rho (p 1) := by
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  have hfun : (fun x => T (annulusPoint x (p 1)) 0) =
      fun x => x + t * eta x * rho (p 1) := by
    funext x
    rw [hvar]
    rfl
  have hd := m64Source_horizontalSlice_hasDerivAt hT (p 0) (p 1)
  rw [hpoint, hfun] at hd
  exact hd.unique ((hasDerivAt_id (p 0)).add
    (((heta (p 0)).hasDerivAt.const_mul t).mul_const (rho (p 1))))

theorem m64LocalizedSource_radial_derivative
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    {eta rho : ℝ → ℝ} (hrho : Differentiable ℝ rho) {t : ℝ}
    (hvar : ∀ x s, T (annulusPoint x s) = annulusPoint (x + t * eta x * rho s) s)
    (p : LoopPlane) :
    fderiv ℝ T p e1 0 = t * eta (p 0) * deriv rho (p 1) := by
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  have hfun : (fun s => T (annulusPoint (p 0) s) 0) =
      fun s => p 0 + t * eta (p 0) * rho s := by
    funext s
    rw [hvar]
    rfl
  have hd := m64Source_verticalSlice_hasDerivAt hT (p 0) (p 1)
  rw [hpoint, hfun] at hd
  exact hd.unique (((hrho (p 1)).hasDerivAt.const_mul (t * eta (p 0))).const_add (p 0))

theorem m64LocalizedSourceInverse_first_tendsto
    (T : ℝ → LoopPlane ≃ₜ LoopPlane) (hsecond : ∀ t p, T t p 1 = p 1)
    (eta rho : ℝ → ℝ) {C : ℝ} (hC : ∀ x, |eta x| ≤ C)
    (hvar : ∀ᶠ t : ℝ in 𝓝 0, ∀ x s,
      T t (annulusPoint x s) = annulusPoint (x + t * eta x * rho s) s)
    (p : LoopPlane) : Tendsto (fun t => (T t).symm p 0) (𝓝 0) (𝓝 (p 0)) := by
  let tau := fun t => m64TriangularSourceSlice (T t) (hsecond t) (p 1)
  let theta := fun x => eta x * rho (p 1)
  have hb (x : ℝ) : |theta x| ≤ C * |rho (p 1)| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
  have hv : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, tau t x = x + t * theta x := by
    filter_upwards [hvar] with t ht x
    change T t (annulusPoint x (p 1)) 0 = x + t * (eta x * rho (p 1))
    rw [ht]
    change x + t * eta x * rho (p 1) = _
    ring
  have h := m64HorizontalSourceInverse_tendsto tau theta hb hv (p 0)
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  change Tendsto (fun t => (T t).symm (annulusPoint (p 0) (p 1)) 0) (𝓝 0) (𝓝 (p 0)) at h
  simpa only [hpoint] using h

end PoincareConjecture
