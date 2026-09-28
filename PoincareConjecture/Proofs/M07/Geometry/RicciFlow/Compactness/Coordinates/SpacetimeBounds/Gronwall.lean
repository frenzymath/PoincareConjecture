import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace PoincareConjecture.SpacetimeBounds

theorem norm_le_exp_of_affine_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {J : Set ℝ} (hJ : Convex ℝ J) (h0 : (0 : ℝ) ∈ J)
    (hf : ∀ t ∈ J, DifferentiableAt ℝ f t)
    {C K D : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hinit : ‖f 0‖ ≤ D)
    (hbound : ∀ t ∈ J, ‖deriv f t‖ ≤ C + K * ‖f t‖)
    {t : ℝ} (ht : t ∈ J) :
    ‖f t‖ ≤ max D 1 * Real.exp ((C + K) * |t|) := by
  let q : ℝ → E × ℝ := fun s => (f (s * t), 1)
  let q' : ℝ → E × ℝ := fun s => (t • deriv f (s * t), 0)
  have hseg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : s * t ∈ J := by
    simpa only [smul_eq_mul, mul_zero, zero_add] using
      hJ h0 ht (sub_nonneg.mpr hs.2) hs.1 (by ring : (1 - s) + s = 1)
  have hq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt q (q' s) s := by
    have hline := (hasDerivAt_id s).mul_const t
    have hcomp := ((hf _ (hseg hs)).hasDerivAt.scomp s hline).prodMk
      (hasDerivAt_const s (1 : ℝ))
    simpa only [q, q', one_mul, Function.comp_def, id_eq] using hcomp
  have hqbound {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖q' s‖ ≤ ((C + K) * |t|) * ‖q s‖ + 0 := by
    have hinit' : C ≤ C * max ‖f (s * t)‖ 1 := by
      simpa using mul_le_mul_of_nonneg_left (le_max_right ‖f (s * t)‖ 1) hC
    have hlinear : K * ‖f (s * t)‖ ≤ K * max ‖f (s * t)‖ 1 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hK
    have hderiv : ‖deriv f (s * t)‖ ≤ (C + K) * max ‖f (s * t)‖ 1 := by
      nlinarith only [hbound _ (hseg hs), hinit', hlinear]
    simpa only [q', q, Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs,
      max_eq_left (mul_nonneg (abs_nonneg t) (norm_nonneg _)),
      norm_one, add_zero, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hderiv (abs_nonneg t)
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun s hs => (hq hs).continuousAt.continuousWithinAt)
    (fun s hs => (hq (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (show ‖q 0‖ ≤ max D 1 by simpa [q, Prod.norm_def] using max_le_max hinit (le_refl (1 : ℝ)))
    (fun s hs => hqbound (Ico_subset_Icc_self hs)) 1 (by constructor <;> norm_num)
  rw [gronwallBound_ε0] at hgr
  have hnorm : ‖f t‖ ≤ ‖q 1‖ := by
    simpa only [q, one_mul] using norm_fst_le (q 1)
  exact hnorm.trans (by simpa using hgr)

end PoincareConjecture.SpacetimeBounds
