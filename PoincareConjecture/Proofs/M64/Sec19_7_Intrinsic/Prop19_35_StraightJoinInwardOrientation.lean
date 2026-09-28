import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedInwardSign

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem reverse_arc_data
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {a b : ℝ}
    (hinj : InjOn gamma (Icc a b))
    (hregular : ∀ t ∈ Ioo a b, deriv gamma t ≠ 0)
    {K U : Set AnnulusCoordinates} (havoid : ∀ t ∈ Ioo a b, gamma t ∉ K)
    (hray : ∀ t ∈ Ioo a b, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      gamma t + r • ((-1 : ℝ) • quarterTurn (deriv gamma t)) ∈ U) :
    let g := fun t => gamma (a + b - t)
    ContDiff ℝ ∞ g ∧ InjOn g (Icc a b) ∧ g '' Icc a b = gamma '' Icc a b ∧
      (∀ t ∈ Ioo a b, deriv g t ≠ 0) ∧
      (∀ t ∈ Ioo a b, g t ∉ K) ∧
      ∀ t ∈ Ioo a b, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        g t + r • quarterTurn (deriv g t) ∈ U := by
  intro g
  have ht' (t : ℝ) (ht : t ∈ Ioo a b) : a + b - t ∈ Ioo a b :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨hg.comp (contDiff_const.sub contDiff_id), ?_, ?_, ?_,
    fun t ht => havoid _ (ht' t ht), ?_⟩
  · intro s hs t ht heq
    have he := hinj ⟨by linarith [hs.2], by linarith [hs.1]⟩
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
    linarith
  · change (gamma ∘ fun t => a + b - t) '' Icc a b = _
    rw [image_comp, image_const_sub_Icc]
    congr 2 <;> ring
  · intro t ht
    change deriv (fun s => gamma (a + b - s)) t ≠ 0
    rw [deriv_comp_const_sub]
    exact neg_ne_zero.mpr (hregular _ (ht' t ht))
  · intro t ht
    simpa only [g, deriv_comp_const_sub, map_neg, neg_one_smul] using hray _ (ht' t ht)

theorem m64Intrinsic_exists_straight_join_inward_orientation
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {A0 A B B1 c : ℝ} (haA : A0 < A) (hBb : B < B1) (hc : 0 < c)
    (hai : InjOn alpha (Icc A0 A)) (hbi : InjOn beta (Icc B B1))
    (hend : alpha A = beta B) (hreg : deriv alpha A ≠ 0)
    (htan : deriv beta B = c • deriv alpha A)
    (hmeet : ∀ s ∈ Icc A0 A, ∀ t ∈ Icc B B1,
      alpha s = beta t → s = A ∧ t = B)
    (hregularA : ∀ t ∈ Ioo A0 A, deriv alpha t ≠ 0)
    (hregularB : ∀ t ∈ Ioo B B1, deriv beta t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha A ∉ K)
    (havoidA : ∀ t ∈ Ioo A0 A, alpha t ∉ K)
    (havoidB : ∀ t ∈ Ioo B B1, beta t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc A0 A ∪ beta '' Icc B B1 ∪ K)
    (hfV : frontier V = frontier U) :
    ∃ (g h : ℝ → AnnulusCoordinates) (a0 a b b1 d : ℝ),
      ((g = alpha ∧ h = beta ∧ a0 = A0 ∧ a = A ∧ b = B ∧ b1 = B1 ∧ d = c) ∨
       (g = (fun t => beta (B + B1 - t)) ∧ h = (fun t => alpha (A0 + A - t)) ∧
        a0 = B ∧ a = B1 ∧ b = A0 ∧ b1 = A ∧ d = c⁻¹)) ∧
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧ a0 < a ∧ b < b1 ∧ 0 < d ∧
      InjOn g (Icc a0 a) ∧ InjOn h (Icc b b1) ∧ g a = h b ∧ g a = alpha A ∧
      deriv g a ≠ 0 ∧ deriv h b = d • deriv g a ∧
      (∀ s ∈ Icc a0 a, ∀ t ∈ Icc b b1, g s = h t → s = a ∧ t = b) ∧
      (∀ t ∈ Ioo a0 a, deriv g t ≠ 0) ∧ (∀ t ∈ Ioo b b1, deriv h t ≠ 0) ∧
      (∀ t ∈ Ioo a0 a, g t ∉ K) ∧ (∀ t ∈ Ioo b b1, h t ∉ K) ∧
      frontier U = g '' Icc a0 a ∪ h '' Icc b b1 ∪ K ∧
      (∀ t ∈ Ioo a0 a, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        g t + r • quarterTurn (deriv g t) ∈ U) ∧
      ∀ t ∈ Ioo b b1, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        h t + r • quarterTurn (deriv h t) ∈ U := by
  obtain ⟨sigma, hsigma, hrayA, hrayB⟩ := m64Intrinsic_exists_straight_join_inward_sign
    ha hb haA hBb hc hai hbi hend hreg htan hmeet hregularA hregularB
    hK hpK havoidA havoidB hU hV hUV hfront hfV
  rcases hsigma with rfl | rfl
  · exact ⟨alpha, beta, A0, A, B, B1, c, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ha, hb, haA, hBb, hc, hai, hbi, hend, rfl, hreg, htan, hmeet,
      hregularA, hregularB, havoidA, havoidB, hfront,
      by simpa only [one_smul] using hrayA, by simpa only [one_smul] using hrayB⟩
  · let g := fun t => beta (B + B1 - t)
    let h := fun t => alpha (A0 + A - t)
    obtain ⟨hg, hgi, hgimage, hgreg, hgavoid, hgray⟩ :=
      reverse_arc_data hb hbi hregularB havoidB hrayB
    obtain ⟨hh, hhi, hhimage, hhreg, hhavoid, hhray⟩ :=
      reverse_arc_data ha hai hregularA havoidA hrayA
    have hgend : g B1 = alpha A := by simp only [g, add_sub_cancel_right, hend]
    have hhend : h A0 = alpha A := by simp only [h, add_sub_cancel_left]
    have hgd : deriv g B1 = -(c • deriv alpha A) := by
      simp only [g, deriv_comp_const_sub, add_sub_cancel_right, htan]
    have hhd : deriv h A0 = -deriv alpha A := by
      simp only [h, deriv_comp_const_sub, add_sub_cancel_left]
    have hgregEnd : deriv g B1 ≠ 0 := by
      rw [hgd]
      exact neg_ne_zero.mpr (smul_ne_zero hc.ne' hreg)
    have htan' : deriv h A0 = c⁻¹ • deriv g B1 := by
      rw [hhd, hgd, smul_neg, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    refine ⟨g, h, B, B1, A0, A, c⁻¹,
      Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hg, hh, hBb, haA, inv_pos.mpr hc,
      hgi, hhi, hgend.trans hhend.symm, hgend, hgregEnd, htan', ?_,
      hgreg, hhreg, hgavoid, hhavoid, ?_, hgray, hhray⟩
    · intro s hs t ht heq
      obtain ⟨ht', hs'⟩ := hmeet (A0 + A - t)
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ (B + B1 - s)
        ⟨by linarith [hs.2], by linarith [hs.1]⟩ heq.symm
      exact ⟨by linarith, by linarith⟩
    · rw [hgimage, hhimage, hfront, union_comm (alpha '' Icc A0 A) (beta '' Icc B B1)]

end PoincareConjecture
