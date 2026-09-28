import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Gronwall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology

namespace PoincareConjecture.M28

theorem norm_le_exp_of_affine_deriv_bound_closed_backward
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {tau C K D : ℝ} (htau : 0 ≤ tau)
    (hf : ContinuousOn f (Icc (-tau) 0))
    (hdiff : ∀ s ∈ Ioo (-tau) 0, DifferentiableAt ℝ f s)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hinit : ‖f 0‖ ≤ D)
    (hbound : ∀ s ∈ Ioo (-tau) 0, ‖deriv f s‖ ≤ C + K * ‖f s‖)
    {t : ℝ} (ht : t ∈ Icc (-tau) 0) :
    ‖f t‖ ≤ max D 1 * Real.exp ((C + K) * tau) := by
  by_cases hzero : tau = 0
  · subst tau
    have ht0 : t = 0 := le_antisymm ht.2 (by simpa using ht.1)
    subst t
    simpa using hinit.trans (le_max_left D 1)
  have htau' : 0 < tau := lt_of_le_of_ne htau (Ne.symm hzero)
  have hinterior (u : ℝ) (hu : u ∈ Ioo (-tau) 0)
      (v : ℝ) (hv : v ∈ Ioo (-tau) 0) :
      ‖f v‖ ≤ max ‖f u‖ 1 * Real.exp ((C + K) * tau) := by
    have hshift (s : ℝ) (hs : s ∈ Ioo (-tau - u) (-u)) :
        s + u ∈ Ioo (-tau) 0 := by constructor <;> linarith [hs.1, hs.2]
    have hderiv (s : ℝ) (hs : s ∈ Ioo (-tau - u) (-u)) :
        HasDerivAt (fun z => f (z + u)) (deriv f (s + u)) s := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hdiff _ (hshift s hs)).hasDerivAt.scomp s
        ((hasDerivAt_id s).add_const u)
    have hgr := SpacetimeBounds.norm_le_exp_of_affine_deriv_bound
      (convex_Ioo (-tau - u) (-u))
      (show (0 : ℝ) ∈ Ioo (-tau - u) (-u) by constructor <;> linarith [hu.1, hu.2])
      (fun s hs => (hderiv s hs).differentiableAt) hC hK
      (show ‖f (0 + u)‖ ≤ ‖f u‖ by simp)
      (fun s hs => by rw [(hderiv s hs).deriv]; exact hbound _ (hshift s hs))
      (show v - u ∈ Ioo (-tau - u) (-u) by constructor <;> linarith [hv.1, hv.2])
    simp only [sub_add_cancel] at hgr
    apply hgr.trans
    apply mul_le_mul_of_nonneg_left _ (le_max_of_le_left (norm_nonneg _))
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (add_nonneg hC hK)
    exact abs_le.mpr ⟨by linarith [hu.2, hv.1], by linarith [hu.1, hv.2]⟩
  have hclosure : closure (Ioo (-tau) (0 : ℝ)) = Icc (-tau) 0 :=
    closure_Ioo (by linarith)
  have h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨by linarith, le_rfl⟩
  have h0closure : (0 : ℝ) ∈ closure (Ioo (-tau) 0) := by rwa [hclosure]
  have hterminal (v : ℝ) (hv : v ∈ Ioo (-tau) 0) :
      ‖f v‖ ≤ max D 1 * Real.exp ((C + K) * tau) := by
    have hcont : ContinuousWithinAt
        (fun u => max ‖f u‖ 1 * Real.exp ((C + K) * tau)) (Ioo (-tau) 0) 0 :=
      (((hf 0 h0).mono Ioo_subset_Icc_self).norm.max continuousWithinAt_const).mul_const _
    have hlim : ‖f v‖ ≤ max ‖f 0‖ 1 * Real.exp ((C + K) * tau) :=
      ContinuousWithinAt.closure_le h0closure continuousWithinAt_const hcont
        (fun u hu => hinterior u hu v hv)
    exact hlim.trans (mul_le_mul_of_nonneg_right
      (max_le_max hinit le_rfl) (Real.exp_pos _).le)
  exact ContinuousWithinAt.closure_le (by rwa [hclosure])
    ((hf t ht).mono Ioo_subset_Icc_self).norm continuousWithinAt_const hterminal

end PoincareConjecture.M28
