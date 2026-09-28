import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedInwardPropagation





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture






theorem m64Intrinsic_exists_straight_join_inward_sign
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
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      (∀ t ∈ Ioo A0 A, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        alpha t + r • (sigma • quarterTurn (deriv alpha t)) ∈ U) ∧
      ∀ t ∈ Ioo B B1, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        beta t + r • (sigma • quarterTurn (deriv beta t)) ∈ U := by
  have hKA : IsCompact (beta '' Icc B B1 ∪ K) :=
    (isCompact_Icc.image hb.continuous).union hK
  have hKB : IsCompact (alpha '' Icc A0 A ∪ K) :=
    (isCompact_Icc.image ha.continuous).union hK
  have havoidA' (s : ℝ) (hs : s ∈ Ioo A0 A) : alpha s ∉ beta '' Icc B B1 ∪ K := by
    rintro (⟨t, ht, heq⟩ | hp)
    · exact hs.2.ne (hmeet s (Ioo_subset_Icc_self hs) t ht heq.symm).1
    · exact havoidA s hs hp
  have havoidB' (t : ℝ) (ht : t ∈ Ioo B B1) : beta t ∉ alpha '' Icc A0 A ∪ K := by
    rintro (⟨s, hs, heq⟩ | hp)
    · exact ht.1.ne' (hmeet s hs t (Ioo_subset_Icc_self ht) heq).2
    · exact havoidB t ht hp
  have hfrontA : frontier U = alpha '' Icc A0 A ∪ (beta '' Icc B B1 ∪ K) := by
    rw [hfront, union_assoc]
  have hfrontB : frontier U = beta '' Icc B B1 ∪ (alpha '' Icc A0 A ∪ K) := by
    rw [hfront]
    ac_rfl
  obtain ⟨sigma, hsigma, hrayA⟩ := m64Intrinsic_exists_global_arc_inward_sign
    ha haA hai hregularA hKA havoidA' hU hV hUV hfrontA hfV
  rcases hsigma with rfl | rfl
  · have hrayA' : ∀ t ∈ Ioo A0 A, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        alpha t + r • quarterTurn (deriv alpha t) ∈ U := by
      simpa only [one_smul] using hrayA
    refine ⟨1, Or.inl rfl, hrayA, ?_⟩
    simpa only [one_smul] using m64Intrinsic_straight_join_inward_propagation
      ha hb haA hBb hc hai hbi hend hreg htan hmeet hregularA hregularB
      hK hpK havoidB hU hV hUV hfront hfV hrayA'
  · obtain ⟨tau, htau, hrayAV⟩ := m64Intrinsic_exists_global_arc_inward_sign
      ha haA hai hregularA hKA havoidA' hV hU hUV.symm (hfV.trans hfrontA) hfV.symm
    have hrayAV' : ∀ t ∈ Ioo A0 A, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        alpha t + r • quarterTurn (deriv alpha t) ∈ V := by
      rcases htau with rfl | rfl
      · simpa only [one_smul] using hrayAV
      · exfalso
        have hp : (A0 + A) / 2 ∈ Ioo A0 A := ⟨by linarith, by linarith⟩
        obtain ⟨r, hrU, hrV⟩ := ((hrayA _ hp).and (hrayAV _ hp)).exists
        exact disjoint_left.mp hUV hrU hrV
    have hrayBV := m64Intrinsic_straight_join_inward_propagation
      ha hb haA hBb hc hai hbi hend hreg htan hmeet hregularA hregularB
      hK hpK havoidB hV hU hUV.symm (hfV.trans hfront) hfV.symm hrayAV'
    obtain ⟨tauB, htauB, hrayBU⟩ := m64Intrinsic_exists_global_arc_inward_sign
      hb hBb hbi hregularB hKB havoidB' hU hV hUV hfrontB hfV
    rcases htauB with rfl | rfl
    · exfalso
      have hp : (B + B1) / 2 ∈ Ioo B B1 := ⟨by linarith, by linarith⟩
      obtain ⟨r, hrU, hrV⟩ := ((hrayBU _ hp).and (hrayBV _ hp)).exists
      exact disjoint_left.mp hUV (by simpa only [one_smul] using hrU) hrV
    · exact ⟨-1, Or.inr rfl, hrayA, hrayBU⟩

end PoincareConjecture
