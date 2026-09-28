import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace PoincareConjecture

theorem m64_deriv_eq_radial_of_eqOn_Icc
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : E → F} (he : DifferentiableAt ℝ e 0)
    {gamma : ℝ → F} (hg : DifferentiableAt ℝ gamma 0)
    {w : E} {T : ℝ} (hT : 0 < T)
    (hvalue : ∀ t ∈ Icc 0 T, gamma t = e (t • w)) :
    deriv gamma 0 = fderiv ℝ e 0 w := by
  have hpath : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hderiv : HasDerivAt (fun t : ℝ => e (t • w)) (fderiv ℝ e 0 w) 0 := by
    have he' : HasFDerivAt e (fderiv ℝ e 0) ((0 : ℝ) • w) := by
      simpa only [zero_smul] using he.hasFDerivAt
    exact he'.comp_hasDerivAt 0 hpath
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hwithin : HasDerivWithinAt gamma (fderiv ℝ e 0 w) (Icc 0 T) 0 :=
    hderiv.hasDerivWithinAt.congr_of_mem hvalue hz
  exact (hg.derivWithin (uniqueDiffOn_Icc hT 0 hz)).symm.trans
    (hwithin.derivWithin (uniqueDiffOn_Icc hT 0 hz))

theorem m64_radial_terminal_derivative_of_closed_reverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : E → F} {v : E} (he : DifferentiableAt ℝ e v)
    {gamma : ℝ → F} (hg : DifferentiableAt ℝ gamma 0) {T : ℝ}
    (hvalue : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) = gamma (T - T * t)) :
    fderiv ℝ e v v = -T • deriv gamma 0 := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 1 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (1 : ℝ)).smul_const v
  have he' : HasFDerivAt e (fderiv ℝ e v) ((1 : ℝ) • v) := by
    simpa only [one_smul] using he.hasFDerivAt
  have hrad : HasDerivAt (fun t : ℝ => e (t • v)) (fderiv ℝ e v v) 1 :=
    he'.comp_hasDerivAt 1 hline
  have hscalar : HasDerivAt (fun t : ℝ => T - T * t) (-T) 1 := by
    simpa only [id_eq, Pi.sub_apply, mul_one, zero_sub] using!
      (hasDerivAt_const (1 : ℝ) T).sub ((hasDerivAt_id (1 : ℝ)).const_mul T)
  have hg' : HasDerivAt gamma (deriv gamma 0) (T - T * 1) := by
    simpa only [mul_one, sub_self] using hg.hasDerivAt
  have hrev : HasDerivAt (fun t : ℝ => gamma (T - T * t)) (-T • deriv gamma 0) 1 :=
    hg'.scomp 1 hscalar
  have hwithin : HasDerivWithinAt (fun t : ℝ => e (t • v))
      (-T • deriv gamma 0) (Icc 0 1) 1 :=
    hrev.hasDerivWithinAt.congr_of_mem hvalue ⟨zero_le_one, le_rfl⟩
  have huniq := uniqueDiffOn_Icc zero_lt_one 1 (show (1 : ℝ) ∈ Icc 0 1 from
    ⟨zero_le_one, le_rfl⟩)
  exact (hrad.hasDerivWithinAt.derivWithin huniq).symm.trans (hwithin.derivWithin huniq)

end PoincareConjecture
