import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M44

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_derivWithin_le_of_interior {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) {B : ℝ → ℝ} (hB : ContinuousOn B (Icc a b))
    (hbound : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ B t) :
    ∀ t ∈ Icc a b, ‖derivWithin f (Icc a b) t‖ ≤ B t := by
  have hc := (hf.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl).norm
  have hi : ∀ t ∈ Ioo a b, ‖derivWithin f (Icc a b) t‖ ≤ B t := by
    intro t ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact hbound t ht
  simpa only [closure_Ioo hab.ne] using
    le_on_closure hi (by simpa only [closure_Ioo hab.ne] using hc)
      (by simpa only [closure_Ioo hab.ne] using hB)

theorem norm_le_exp_of_affine_derivWithin_bound {f : ℝ → E} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Icc a b)) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hinit : ‖f a‖ ≤ D)
    (hbound : ∀ t ∈ Icc a b, ‖derivWithin f (Icc a b) t‖ ≤ C * (1 + ‖f t‖)) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ D * Real.exp ((2 * C) * (t - a)) := by
  let q : ℝ → E × ℝ := fun t => (f t, 1)
  let d : ℝ → E × ℝ := fun t => (derivWithin f (Icc a b) t, 0)
  have hd (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt q (d t) (Ici t) t := by
    have hq : HasDerivWithinAt q (d t) (Icc a b) t :=
      (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt.prodMk
        (hasDerivWithinAt_const t (Icc a b) (1 : ℝ))
    exact hq.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hrate (t : ℝ) (ht : t ∈ Ico a b) : ‖d t‖ ≤ (2 * C) * ‖q t‖ + 0 := by
    have hmax0 : ‖f t‖ ≤ max ‖f t‖ 1 := le_max_left _ _
    have hmax1 : 1 ≤ max ‖f t‖ 1 := le_max_right _ _
    have hh := hbound t (Ico_subset_Icc_self ht)
    simp only [q, d, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _), norm_one]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hmax0),
      mul_nonneg hC (sub_nonneg.mpr hmax1)]
  have hq : ContinuousOn q (Icc a b) := hf.continuousOn.prodMk continuousOn_const
  have hqa : ‖q a‖ ≤ D := by
    simpa only [q, Prod.norm_def, norm_one] using max_le hinit hD
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hq hd hqa hrate t ht
  rw [gronwallBound_ε0] at h
  exact (norm_fst_le (q t)).trans h

theorem norm_le_exp_of_interior_affine_bound {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hinit : ‖f a‖ ≤ D)
    (hbound : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ C * (1 + ‖f t‖)) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ D * Real.exp ((2 * C) * (b - a)) := by
  have hclosed := norm_derivWithin_le_of_interior hab hf
    (continuousOn_const.mul (continuousOn_const.add hf.continuousOn.norm)) hbound
  intro t ht
  apply (norm_le_exp_of_affine_derivWithin_bound (hf.differentiableOn (by norm_num))
    hC hD hinit hclosed t ht).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ D)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
    (by positivity))

theorem norm_sub_le_of_interior_deriv_bound {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) {C : ℝ}
    (hbound : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ C) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖f t - f s‖ ≤ C * |t - s| := by
  have hclosed := norm_derivWithin_le_of_interior hab hf continuousOn_const hbound
  intro s hs t ht
  simpa only [Real.norm_eq_abs] using (convex_Icc a b).norm_image_sub_le_of_norm_derivWithin_le
    (hf.differentiableOn (by norm_num)) hclosed hs ht

end PoincareConjecture.M44
