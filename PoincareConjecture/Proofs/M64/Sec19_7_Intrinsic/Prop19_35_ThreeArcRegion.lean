import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CrossRayRegion

noncomputable section
set_option autoImplicit false

open Set Function
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_exists_three_arc_region
    {base alpha beta : ℝ → AnnulusCoordinates} {a b A u L : ℝ}
    (hab : a < b) (hA : 0 < A) (huL : u < L)
    (hb : ContinuousOn base (Icc a b)) (ha : Continuous alpha) (hc : Continuous beta)
    (hbi : InjOn base (Icc a b)) (hai : InjOn alpha (Icc 0 A))
    (hci : InjOn beta (Icc u L))
    (hstart : base a = alpha 0) (hend : base b = beta u) (hmeet : alpha A = beta L)
    (hba : ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 A, base x = alpha t → x = a ∧ t = 0)
    (hbc : ∀ x ∈ Icc a b, ∀ t ∈ Icc u L, base x = beta t → x = b ∧ t = u)
    (hac : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc u L, alpha s = beta t → s = A ∧ t = L) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (frontier U)ᶜ ∧ frontier V = frontier U ∧
      IsCompact (closure U) ∧
      frontier U = base '' Icc a b ∪ (alpha '' Icc 0 A ∪ beta '' Icc u L) := by
  let f : ℝ → AnnulusCoordinates := fun x => base ((b - a) * x + a)
  let g : ℝ → AnnulusCoordinates := fun t => beta (u + t)
  have hparam (x : ℝ) (hx : x ∈ Icc 0 1) : (b - a) * x + a ∈ Icc a b :=
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  have htparam (t : ℝ) (ht : t ∈ Icc 0 (L - u)) : u + t ∈ Icc u L :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hf : ContinuousOn f (Icc 0 1) := hb.comp
    ((continuous_const.mul continuous_id).add continuous_const).continuousOn hparam
  have hg : Continuous g := hc.comp (continuous_const.add continuous_id)
  have hfi : InjOn f (Icc 0 1) := by
    intro x hx y hy hxy
    have heq := hbi (hparam x hx) (hparam y hy) hxy
    nlinarith
  have hgi : InjOn g (Icc 0 (L - u)) := by
    intro x hx y hy hxy
    have heq := hci (htparam x hx) (htparam y hy) hxy
    linarith
  have hfa : ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 A,
      f x = alpha t → x = 0 ∧ t = 0 := by
    intro x hx t ht hxt
    have hh := hba _ (hparam x hx) t ht hxt
    exact ⟨by nlinarith [hh.1], hh.2⟩
  have hfg : ∀ x ∈ Icc 0 1, ∀ t ∈ Icc 0 (L - u),
      f x = g t → x = 1 ∧ t = 0 := by
    intro x hx t ht hxt
    have hh := hbc _ (hparam x hx) _ (htparam t ht) hxt
    exact ⟨by nlinarith [hh.1], by linarith [hh.2]⟩
  obtain ⟨s, t, hs, hsA, ht, htL, hst, U, V, hU, hV, hpU, hpV,
      hbU, hbV, hd, hcover, hfU, hfV, hcompact⟩ :=
    m64Intrinsic_exists_crossing_ray_region ha hg hai hgi hf hfi
      (by simpa only [f, mul_zero, zero_add] using hstart)
      (by simpa only [f, g, mul_one, sub_add_cancel, add_zero] using hend)
      hfa hfg ⟨A, ⟨hA.le, le_rfl⟩, L - u, ⟨sub_nonneg.mpr huL.le, le_rfl⟩,
        by simpa only [g, add_sub_cancel] using hmeet⟩
  have hends := hac s ⟨hs.le, hsA⟩ (u + t) (htparam t ⟨ht.le, htL⟩) hst
  have hs' : s = A := hends.1
  have ht' : t = L - u := by linarith [hends.2]
  subst s
  subst t
  have hfimage : f '' Icc 0 1 = base '' Icc a b := by
    change (base ∘ fun x => (b - a) * x + a) '' Icc 0 1 = _
    rw [image_comp, image_affine_Icc' (sub_pos.mpr hab)]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
  have hgimage : g '' Icc 0 (L - u) = beta '' Icc u L := by
    change (beta ∘ fun t => u + t) '' Icc 0 (L - u) = _
    rw [image_comp, image_const_add_Icc]
    simp only [add_zero, add_sub_cancel]
  rw [hfimage, hgimage] at hcover hfU hfV
  exact ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hd,
    by simpa only [hfU] using hcover, hfV.trans hfU.symm, hcompact, hfU⟩

end PoincareConjecture
