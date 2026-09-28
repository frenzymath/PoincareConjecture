import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace PoincareConjecture.SurfaceSoliton

private theorem exp_secant_derivative_pos {x : ℝ} (hx : 0 < x) :
    0 < (x - 1) * Real.exp x + 1 := by
  let F := fun t : ℝ => (t - 1) * Real.exp t + 1
  have hd (t : ℝ) : HasDerivAt F (t * Real.exp t) t := by
    dsimp only [F]
    convert (((hasDerivAt_id t).sub_const 1).mul (Real.hasDerivAt_exp t)).add_const 1 using 1 <;>
      first | rfl | skip
    simp only [id_eq]
    ring
  have hm : StrictMonoOn F (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (show Continuous F by unfold F; fun_prop).continuousOn
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hd t).deriv]
    exact mul_pos ht (Real.exp_pos t)
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx.le) hx
  simpa [F] using h



theorem exp_secant_lt_endpoint_average {x : ℝ} (hx : 0 < x) :
    2 * (Real.exp x - 1) < x * (Real.exp x + 1) := by
  let F := fun t : ℝ => t * (Real.exp t + 1) - 2 * (Real.exp t - 1)
  have hd (t : ℝ) : HasDerivAt F ((t - 1) * Real.exp t + 1) t := by
    dsimp only [F]
    convert ((hasDerivAt_id t).mul ((Real.hasDerivAt_exp t).add_const 1)).sub
      (((Real.hasDerivAt_exp t).sub_const 1).const_mul 2) using 1 <;>
      first | rfl | skip
    simp only [id_eq]
    ring
  have hm : StrictMonoOn F (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (show Continuous F by unfold F; fun_prop).continuousOn
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hd t).deriv]
    exact exp_secant_derivative_pos ht
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx.le) hx
  have h' : 0 < x * (Real.exp x + 1) - 2 * (Real.exp x - 1) := by
    simpa [F] using h
  linarith



theorem critical_values_eq_of_opposite_slopes {a b A lambda : ℝ}
    (hab : a ≤ b) (hA : 0 < A)
    (henergy : A * (Real.exp b - Real.exp a) = 2 * lambda * (b - a))
    (hslopes : A * (Real.exp b + Real.exp a) = 4 * lambda) :
    a = b := by
  by_contra hne
  have hd : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab hne)
  have hstrict := exp_secant_lt_endpoint_average hd
  have hpos : 0 < A * Real.exp a := mul_pos hA (Real.exp_pos a)
  have hstrict' := mul_lt_mul_of_pos_left hstrict hpos
  have hexp : Real.exp a * Real.exp (b - a) = Real.exp b := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hleft : A * Real.exp a * (2 * (Real.exp (b - a) - 1)) =
      2 * (A * (Real.exp b - Real.exp a)) := by
    rw [mul_sub, mul_sub]
    nlinarith [hexp]
  have hright : A * Real.exp a * ((b - a) * (Real.exp (b - a) + 1)) =
      (b - a) * (A * (Real.exp b + Real.exp a)) := by
    calc
      _ = (b - a) * A * (Real.exp a * Real.exp (b - a) + Real.exp a) := by ring
      _ = _ := by rw [hexp]; ring
  rw [hleft, hright, henergy, hslopes] at hstrict'
  nlinarith

end PoincareConjecture.SurfaceSoliton
