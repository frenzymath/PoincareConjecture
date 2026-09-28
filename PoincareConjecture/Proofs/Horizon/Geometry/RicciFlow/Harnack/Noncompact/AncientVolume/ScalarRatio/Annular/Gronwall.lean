import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Gronwall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

namespace PoincareConjecture.SpacetimeBounds

theorem norm_le_exp_of_affine_deriv_bound_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a C K D : ℝ}
    (hcont : ContinuousOn f (Icc a 0))
    (hf : ∀ t ∈ Ioo a 0, DifferentiableAt ℝ f t)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hinit : ‖f 0‖ ≤ D)
    (hbound : ∀ t ∈ Ioo a 0, ‖deriv f t‖ ≤ C + K * ‖f t‖)
    {t : ℝ} (ht : t ∈ Icc a 0) :
    ‖f t‖ ≤ max D 1 * Real.exp ((C + K) * |t|) := by
  have ha : a ≤ 0 := ht.1.trans ht.2
  rcases ha.eq_or_lt with ha | ha
  · have ht0 : t = 0 := le_antisymm ht.2 (ha ▸ ht.1)
    simpa [ht0] using hinit.trans (le_max_left D 1)
  have hbetween {s u : ℝ} (hs : s ∈ Ioo a 0) (hu : u ∈ Ioo a 0) :
      ‖f s‖ ≤ max ‖f u‖ 1 * Real.exp ((C + K) * |s - u|) := by
    let g : ℝ → E := fun v => f (v + u)
    have hmem {v : ℝ} (hv : v ∈ Ioo (a - u) (-u)) : v + u ∈ Ioo a 0 := by
      constructor <;> linarith [hv.1, hv.2]
    have hg {v : ℝ} (hv : v ∈ Ioo (a - u) (-u)) :
        HasDerivAt g (deriv f (v + u)) v := by
      simpa only [g, Function.comp_def, id_eq, one_smul] using
        (hf _ (hmem hv)).hasDerivAt.scomp v ((hasDerivAt_id v).add_const u)
    have h := norm_le_exp_of_affine_deriv_bound
      (convex_Ioo (a - u) (-u))
      (show (0 : ℝ) ∈ Ioo (a - u) (-u) by constructor <;> linarith [hu.1, hu.2])
      (fun v hv => (hg hv).differentiableAt) hC hK
      (show ‖g 0‖ ≤ ‖f u‖ by simp [g])
      (fun v hv => (hg hv).deriv ▸ hbound _ (hmem hv))
      (show s - u ∈ Ioo (a - u) (-u) by constructor <;> linarith [hs.1, hs.2])
    simpa [g] using h
  have hinterior {s : ℝ} (hs : s ∈ Ioo a 0) :
      ‖f s‖ ≤ max D 1 * Real.exp ((C + K) * |s|) := by
    have hzero : (0 : ℝ) ∈ closure (Ioo a 0) := by
      rw [closure_Ioo ha.ne]
      exact ⟨ha.le, le_rfl⟩
    have hright : ContinuousWithinAt
        (fun u => max ‖f u‖ 1 * Real.exp ((C + K) * |s - u|)) (Ioo a 0) 0 := by
      have hc := (hcont 0 ⟨ha.le, le_rfl⟩).mono Ioo_subset_Icc_self
      fun_prop
    have h := ContinuousWithinAt.closure_le hzero continuousWithinAt_const hright
      (fun u hu => hbetween hs hu)
    have h' : ‖f s‖ ≤ max ‖f 0‖ 1 * Real.exp ((C + K) * |s|) := by simpa using h
    exact h'.trans
      (mul_le_mul_of_nonneg_right (max_le_max hinit le_rfl) (Real.exp_nonneg _))
  have htclosure : t ∈ closure (Ioo a 0) := by rwa [closure_Ioo ha.ne]
  apply ContinuousWithinAt.closure_le htclosure
    ((hcont t ht).norm.mono Ioo_subset_Icc_self)
    (by fun_prop)
  exact fun s hs => hinterior hs

end PoincareConjecture.SpacetimeBounds
