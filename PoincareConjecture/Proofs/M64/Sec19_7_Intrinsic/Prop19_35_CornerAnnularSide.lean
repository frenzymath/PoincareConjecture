import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCornerCoordinates













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture




theorem m64Intrinsic_annular_corner_is_convex
    {q : AnnulusCoordinates} (hq : ‖q‖ = 1)
    {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap q) (hzero : phi q = 0)
    (hinward : 0 < inner ℝ q (L.symm (0, 1)))
    {S : Set AnnulusCoordinates} (hS : S ⊆ standardAnnulusDomain)
    (positive : Bool)
    (hregion : ∀ᶠ z in 𝓝 q, z ∈ S ↔
      if positive then 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2
      else (phi z).1 ≤ 0 ∨ (phi z).2 ≤ 0) : positive = true := by
  cases positive
  swap
  · rfl
  exfalso
  let v := L.symm (0, 1)
  have hray : HasDerivAt (fun r : ℝ => q - r • v) (-v) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) q).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hpd : HasDerivAt (fun r : ℝ => (phi (q - r • v)).2) (-1) 0 := by
    have hf : HasFDerivAt (fun z => (phi z).2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap)
        (q - (0 : ℝ) • v) := by simpa only [zero_smul, sub_zero] using hphi.snd
    have hh := hf.comp_hasDerivAt (f := fun r : ℝ => q - r • v) 0 hray
    simpa [v, Function.comp_def] using! hh
  have hpath : Tendsto (fun r : ℝ => q - r • v) (𝓝[>] 0) (𝓝 q) := by
    simpa only [zero_smul, sub_zero] using hray.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r * ‖v‖ ^ 2 < inner ℝ q v := by
    have hc : ContinuousAt (fun r : ℝ => r * ‖v‖ ^ 2) 0 := by fun_prop
    have ht : Tendsto (fun r : ℝ => r * ‖v‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa only [zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually_lt_const hinward
  obtain ⟨r, ⟨⟨hslope, hreg⟩, hrsmall⟩, hrpos⟩ :=
    (hpd.tendsto_slope_zero_right.eventually_lt_const (by norm_num : (-1 : ℝ) < 0) |>.and
      (hpath.eventually hregion) |>.and hsmall |>.and self_mem_nhdsWithin).exists
  have hr : 0 < r := hrpos
  have hnegative : (phi (q - r • v)).2 < 0 := by
    have h0 : (phi q).2 = 0 := congrArg Prod.snd hzero
    simp only [zero_add, zero_smul, sub_zero, h0, smul_eq_mul] at hslope
    have hi := inv_pos.mpr hr
    nlinarith
  have hmem : q - r • v ∈ S := hreg.mpr (Or.inr hnegative.le)
  have hnormge : 1 ≤ ‖q - r • v‖ := (hS hmem).1
  have hnorm : ‖q - r • v‖ ^ 2 =
      1 - 2 * r * inner ℝ q v + r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, inner_smul_right, hq,
      mul_pow, sq_abs]
    ring
  have hprod := mul_lt_mul_of_pos_left hrsmall hr
  nlinarith




theorem m64Intrinsic_exists_annular_two_arc_corner_coordinates
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0)
    (hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha 0 ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ W)
    (hfV : frontier V = frontier U)
    (hnorm : ‖alpha 0‖ = 1) (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)),
      HasFDerivAt phi L.toContinuousLinearMap (alpha 0) ∧ phi (alpha 0) = 0 ∧
      L.symm (1, 0) = deriv alpha 0 ∧ L.symm (0, 1) = deriv beta 0 ∧
      (∀ᶠ z in 𝓝 (alpha 0), z ∈ closure U ↔ 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2) := by
  obtain ⟨phi, L, positive, hd, hzero, hu, hv, hregion⟩ :=
    m64Intrinsic_exists_two_arc_corner_coordinates ha hb hA hB hai hbi hbase hind
      hW hpW hU hV hdisj hfU hfV
  have hpos := m64Intrinsic_annular_corner_is_convex hnorm L hd hzero
    (by simpa only [hv] using hinward) hsub positive hregion
  refine ⟨phi, L, hd, hzero, hu, hv, ?_⟩
  simpa only [hpos, if_true] using hregion

end PoincareConjecture
