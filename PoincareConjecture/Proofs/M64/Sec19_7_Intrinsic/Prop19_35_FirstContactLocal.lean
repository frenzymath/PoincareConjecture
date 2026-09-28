import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GlobalChart
import Mathlib.Analysis.Calculus.Deriv.Slope












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

private theorem negative_derivative_eventually_below
    {f : ℝ → ℝ} {d R : ℝ} (hf : HasDerivAt f d 0)
    (hR : f 0 ≤ R) (hd : f 0 < R ∨ d < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < R := by
  rcases hd with hlt | hneg
  · exact (hf.continuousAt.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
  · have hs := hf.tendsto_slope_zero_right.eventually (gt_mem_nhds hneg)
    filter_upwards [hs, self_mem_nhdsWithin] with t ht hpos
    change 0 < t at hpos
    simp only [zero_add, smul_eq_mul] at ht
    have hlt : f t - f 0 < 0 := by nlinarith [inv_pos.mpr hpos]
    linarith




theorem m64Intrinsic_first_contact_no_common_descent
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u)
    {S : Set (ℝ × ℝ)} (hS : IsOpen S) {p q : ℝ × ℝ} {R : ℝ}
    (hp : p ∈ S) (hq : q ∈ S) (hpheight : p.2 ∈ Ioc (0 : ℝ) R)
    (hqheight : q.2 ∈ Ioc (0 : ℝ) R) (hne : p ≠ q) (hmeet : u p = u q)
    (hinj : InjOn u (S ∩ {z | 0 < z.2 ∧ z.2 < R}))
    (A B : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    (hA : HasFDerivAt u A.toContinuousLinearMap p)
    (hB : HasFDerivAt u B.toContinuousLinearMap q)
    (w : AnnulusCoordinates)
    (hwp : p.2 < R ∨ (A.symm w).2 < 0)
    (hwq : q.2 < R ∨ (B.symm w).2 < 0) : False := by
  have hAs := hu.contDiffAt.hasStrictFDerivAt' hA (by simp)
  have hBs := hu.contDiffAt.hasStrictFDerivAt' hB (by simp)
  let a := hAs.localInverse u A p
  let b := hBs.localInverse u B q
  let line := fun t : ℝ => u p + t • w
  have hline : HasDerivAt line w 0 := by
    simpa only [line, one_smul, zero_add, id_eq] using!
      (hasDerivAt_const (0 : ℝ) (u p)).add ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have hline0 : line 0 = u p := by simp only [line, zero_smul, add_zero]
  have ha : HasDerivAt (a ∘ line) (A.symm w) 0 :=
    hAs.to_localInverse.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hline0.symm
  have hb : HasDerivAt (b ∘ line) (B.symm w) 0 :=
    hBs.to_localInverse.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (hline0.trans hmeet).symm
  have ha0 : a (line 0) = p := by rw [hline0]; exact hAs.localInverse_apply_image
  have hb0 : b (line 0) = q := by rw [hline0, hmeet]; exact hBs.localInverse_apply_image
  have haS : ∀ᶠ t in 𝓝 (0 : ℝ), a (line t) ∈ S :=
    ha.continuousAt.eventually (by
      change S ∈ 𝓝 (a (line 0))
      rw [ha0]
      exact hS.mem_nhds hp)
  have hbS : ∀ᶠ t in 𝓝 (0 : ℝ), b (line t) ∈ S :=
    hb.continuousAt.eventually (by
      change S ∈ 𝓝 (b (line 0))
      rw [hb0]
      exact hS.mem_nhds hq)
  have hapos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (a (line t)).2 :=
    ha.continuousAt.snd.eventually (lt_mem_nhds (by simpa only [Function.comp_apply, ha0]
      using hpheight.1))
  have hbpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (b (line t)).2 :=
    hb.continuousAt.snd.eventually (lt_mem_nhds (by simpa only [Function.comp_apply, hb0]
      using hqheight.1))
  have halt := negative_derivative_eventually_below ha.snd
    (by simpa only [Function.comp_apply, ha0] using hpheight.2)
    (by simpa only [Function.comp_apply, ha0] using hwp)
  have hblt := negative_derivative_eventually_below hb.snd
    (by simpa only [Function.comp_apply, hb0] using hqheight.2)
    (by simpa only [Function.comp_apply, hb0] using hwq)
  have hab : ∀ᶠ t in 𝓝 (0 : ℝ), a (line t) ≠ b (line t) :=
    (ha.continuousAt.prodMk hb.continuousAt).eventually
      ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds
        (by change a (line 0) ≠ b (line 0); rw [ha0, hb0]; exact hne))
  have hia : ∀ᶠ t in 𝓝 (0 : ℝ), u (a (line t)) = line t :=
    hline.continuousAt.tendsto.eventually (hline0.symm ▸ hAs.eventually_right_inverse)
  have hib : ∀ᶠ t in 𝓝 (0 : ℝ), u (b (line t)) = line t :=
    hline.continuousAt.tendsto.eventually
      ((hline0.trans hmeet).symm ▸ hBs.eventually_right_inverse)
  have hfalse : ∀ᶠ t in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [halt, hblt, haS.filter_mono nhdsWithin_le_nhds,
      hbS.filter_mono nhdsWithin_le_nhds, hapos.filter_mono nhdsWithin_le_nhds,
      hbpos.filter_mono nhdsWithin_le_nhds, hab.filter_mono nhdsWithin_le_nhds,
      hia.filter_mono nhdsWithin_le_nhds, hib.filter_mono nhdsWithin_le_nhds]
      with t hat hbt has hbs hap hbp habt hiat hibt
    exact habt (hinj ⟨has, hap, hat⟩ ⟨hbs, hbp, hbt⟩ (hiat.trans hibt.symm))
  exact hfalse.exists.elim (fun _ h => h)

end PoincareConjecture
