import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcSignedInwardRay
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcInwardOrientation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_StraightJoinOccupiedStrips




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture






theorem m64Intrinsic_straight_join_inward_propagation
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
    (havoidB : ∀ t ∈ Ioo B B1, beta t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc A0 A ∪ beta '' Icc B B1 ∪ K)
    (hfV : frontier V = frontier U)
    (hrayA : ∀ t ∈ Ioo A0 A, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      alpha t + r • quarterTurn (deriv alpha t) ∈ U) :
    ∀ t ∈ Ioo B B1, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      beta t + r • quarterTurn (deriv beta t) ∈ U := by
  have hother : IsCompact (alpha '' Icc A0 A ∪ K) :=
    (isCompact_Icc.image ha.continuous).union hK
  have havoid (t : ℝ) (ht : t ∈ Ioo B B1) : beta t ∉ alpha '' Icc A0 A ∪ K := by
    rintro (⟨s, hs, heq⟩ | hp)
    · exact ht.1.ne' (hmeet s hs t (Ioo_subset_Icc_self ht) heq).2
    · exact havoidB t ht hp
  have hfrontB : frontier U = beta '' Icc B B1 ∪ (alpha '' Icc A0 A ∪ K) := by
    rw [hfront]
    ac_rfl
  obtain ⟨sigma, hsigma, hrayB⟩ := m64Intrinsic_exists_global_arc_inward_sign
    hb hBb hbi hregularB hother havoid hU hV hUV hfrontB hfV
  rcases hsigma with rfl | rfl
  · simpa only [one_smul] using hrayB
  · exfalso
    let w := quarterTurn (deriv alpha A)
    have hw : w ≠ 0 := by
      intro hz
      exact hreg (quarterTurn.injective (by simpa only [map_zero] using hz))
    have hposB : 0 < inner ℝ (quarterTurn (deriv beta B)) w := by
      rw [htan, map_smul, real_inner_smul_left]
      exact mul_pos hc (real_inner_self_pos.mpr hw)
    have hcont : Continuous (fun t => inner ℝ (quarterTurn (deriv beta t)) w) :=
      (quarterTurn.continuous.comp (contDiff_infty_iff_deriv.mp hb).2.continuous).inner
        continuous_const
    have hnear : ∀ᶠ t in 𝓝 B, 0 < inner ℝ (quarterTurn (deriv beta t)) w :=
      hcont.continuousAt.eventually (isOpen_Ioi.mem_nhds hposB)
    obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hnear
    obtain ⟨epsilon, hepsilon, heradius, _, hbeps, L, R, G, H, f, g, hf, hg,
        P, Q, delta, hdelta, _, _, _, _, _, hgraphB, _, _, _, hinsideB, _, _⟩ :=
      m64Intrinsic_exists_straight_join_occupied_strips ha hb haA hBb hc hradius hai hbi
        hend hreg htan hmeet hregularA hK hpK hU hV hUV hfront hfV hrayA
    have hp : B + epsilon ∈ Ioo B B1 := ⟨lt_add_of_pos_right _ hepsilon, hbeps⟩
    have hpos : 0 < inner ℝ (quarterTurn (deriv beta (B + epsilon))) w := by
      apply hball
      simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos hepsilon]
        using heradius
    obtain ⟨cutoff, hcutoff, hcut⟩ :=
      Q.right.exists_small_positive_parameters (lt_min hdelta Q.radius_pos)
    have hphysical : ∀ᶠ r in 𝓝[>] (0 : ℝ), beta (B + epsilon) + r • w ∈ closure U := by
      filter_upwards [Ioo_mem_nhdsGT hcutoff] with r hr
      have hq := hcut r hr
      have hz : Q.right.parameter r ∈ Ioo (-Q.radius) Q.radius :=
        ⟨by linarith [hq.2.1, Q.radius_pos], hq.2.2.trans_le (min_le_right _ _)⟩
      have hi := (hinsideB 1 (by simp) (Q.right.parameter r)
        ⟨hq.2.1.le, (hq.2.2.trans_le (min_le_left _ _)).le⟩).2.1
      rw [Q.linearCoordinates_right R.symm H.open_target hg hz,
        Q.right.parameter.left_inv hq.1,
        ← hgraphB.2.2.2.1 _ (hgraphB.1 (right_mem_Icc.mpr hp.1.le)), R.symm_apply_apply] at hi
      simpa only [Prod.eta, R.symm_apply_apply] using hi
    have hsign := m64Intrinsic_arc_signed_inward_ray_transverse_pos hb hbi hp hregularB
      hother (havoid _ hp) hU hV hUV hfrontB hfV (Or.inr rfl) (hrayB _ hp)
      (w := w) (by simpa only [neg_one_smul, inner_neg_left] using neg_ne_zero.mpr hpos.ne')
      hphysical
    simp only [neg_one_smul, inner_neg_left] at hsign
    linarith

end PoincareConjecture
