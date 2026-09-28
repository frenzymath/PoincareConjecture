import PoincareConjecture.Proofs.M25.Mathlib.SecondDerivative
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring










set_option autoImplicit false

open Set
open scoped ContDiff





theorem norm_fderiv_fderiv_comp_le_of_contDiffOn
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F} {g : F → G} {U : Set E} {V : Set F} {x : E}
    (hU : IsOpen U) (hV : IsOpen V) (hx : x ∈ U)
    (hf : ContDiffOn 𝕜 2 f U) (hg : ContDiffOn 𝕜 2 g V)
    (hmap : MapsTo f U V) :
    ‖fderiv 𝕜 (fderiv 𝕜 (g ∘ f)) x‖ ≤
      ‖fderiv 𝕜 (fderiv 𝕜 g) (f x)‖ * ‖fderiv 𝕜 f x‖ ^ 2 +
        ‖fderiv 𝕜 g (f x)‖ * ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [fderiv_fderiv_comp_apply_of_contDiffOn hU hV hx hf hg hmap v w]
  let A := fderiv 𝕜 f x
  let B := fderiv 𝕜 (fderiv 𝕜 f) x
  let C := fderiv 𝕜 g (f x)
  let D := fderiv 𝕜 (fderiv 𝕜 g) (f x)
  change ‖D (A v) (A w) + C (B v w)‖ ≤
    (‖D‖ * ‖A‖ ^ 2 + ‖C‖ * ‖B‖) * ‖v‖ * ‖w‖
  have hleft : ‖D (A v) (A w)‖ ≤ ‖D‖ * (‖A‖ * ‖v‖) * (‖A‖ * ‖w‖) := by
    calc
      _ ≤ ‖D‖ * ‖A v‖ * ‖A w‖ := D.le_opNorm₂ _ _
      _ ≤ ‖D‖ * (‖A‖ * ‖v‖) * (‖A‖ * ‖w‖) := by
        gcongr <;> exact A.le_opNorm _
  have hright : ‖C (B v w)‖ ≤ ‖C‖ * (‖B‖ * ‖v‖ * ‖w‖) :=
    (C.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (B.le_opNorm₂ v w) (norm_nonneg C))
  exact (norm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))
