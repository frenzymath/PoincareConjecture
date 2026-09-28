import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Shift










set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture.M34



theorem norm_le_exp_of_interior_affine_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {T C : ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ f t) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Ioo 0 T, ‖deriv f t‖ ≤ C * (1 + ‖f t‖))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖f t‖ ≤ max ‖f 0‖ 1 * Real.exp (2 * C * t) := by
  by_cases hT : 0 < T
  · have hinter (s : ℝ) (hs : s ∈ Ioo 0 T) :
        ‖f s‖ ≤ max ‖f 0‖ 1 * Real.exp (2 * C * s) := by
      have hshift (e : ℝ) (he : e ∈ Ioo 0 s) :
          ‖f s‖ ≤ max ‖f e‖ 1 * Real.exp (2 * C * (s - e)) := by
        have hmem (u : ℝ) (hu : u ∈ Icc 0 (s - e)) : e + u ∈ Ioo 0 T := by
          constructor <;> linarith [he.1, he.2, hu.1, hu.2, hs.2]
        have hg := SpacetimeBounds.norm_le_exp_of_affine_deriv_bound
          (f := fun u => f (e + u)) (convex_Icc 0 (s - e))
          (show (0 : ℝ) ∈ Icc 0 (s - e) by constructor <;> linarith [he.2])
          (fun u hu => ((hd _ (hmem u hu)).hasDerivAt.comp_const_add e u).differentiableAt)
          hC hC (show ‖f (e + 0)‖ ≤ ‖f e‖ by simp)
          (fun u hu => by
            simpa only [deriv_comp_const_add, mul_add, mul_one] using hb _ (hmem u hu))
          (show s - e ∈ Icc 0 (s - e) by constructor <;> linarith [he.2])
        simpa only [add_sub_cancel, abs_of_nonneg (sub_nonneg.mpr he.2.le),
          ← two_mul C] using hg
      have hsub : Ioo 0 s ⊆ Icc 0 T :=
        fun _ hu => ⟨hu.1.le, hu.2.le.trans hs.2.le⟩
      have hezero : (0 : ℝ) ∈ closure (Ioo 0 s) := by
        rw [closure_Ioo hs.1.ne]
        exact ⟨le_rfl, hs.1.le⟩
      have hfzero := (hf 0 ⟨le_rfl, hT.le⟩).mono hsub
      have hexp : Continuous (fun e : ℝ => Real.exp (2 * C * (s - e))) := by fun_prop
      have hright : ContinuousWithinAt
          (fun e : ℝ => max ‖f e‖ 1 * Real.exp (2 * C * (s - e))) (Ioo 0 s) 0 :=
        (hfzero.norm.max continuousWithinAt_const).mul hexp.continuousWithinAt
      simpa only [sub_zero] using
        ContinuousWithinAt.closure_le hezero continuousWithinAt_const hright hshift
    have htclosure : t ∈ closure (Ioo 0 T) := by rwa [closure_Ioo hT.ne]
    exact ContinuousWithinAt.closure_le htclosure
      ((hf t ht).mono Ioo_subset_Icc_self).norm
      (by fun_prop) hinter
  · have htzero : t = 0 := le_antisymm (ht.2.trans (le_of_not_gt hT)) ht.1
    subst t
    simp only [mul_zero, Real.exp_zero, mul_one]
    exact le_max_left _ _

end PoincareConjecture.M34
