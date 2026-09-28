import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseArcCuts
import Mathlib.Analysis.Calculus.Deriv.Slope













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem eventually_positive_of_derivative
    {f : ℝ → ℝ} {v : ℝ} (hf : HasDerivAt f v 0) (hzero : f 0 = 0) (hv : 0 < v) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < f r := by
  have hs := hf.tendsto_slope_zero_right.eventually_const_lt hv
  filter_upwards [hs, self_mem_nhdsWithin] with r hr hrpos
  have hrpos' : 0 < r := hrpos
  simp only [zero_add, hzero, sub_zero, smul_eq_mul] at hr
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hrpos')).mp hr





theorem m64Intrinsic_transverse_ray_enters_region
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hfront : frontier U = gamma '' Icc 0 T)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      gamma t + r • quarterTurn (deriv gamma t) ∈ U)
    (hp : p ∈ Ioo (0 : ℝ) T) {w : AnnulusCoordinates}
    (hw : 0 < inner ℝ (quarterTurn (deriv gamma p)) w) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • w ∈ U := by
  let a := p / 2
  let b := (p + T) / 2
  have ha : 0 < a := half_pos hp.1
  have hap : a < p := half_lt_self hp.1
  have hpb : p < b := by dsimp [b]; linarith [hp.2]
  have hb : b < T := by dsimp [b]; linarith [hp.2]
  have hab : a ≤ b := (hap.trans hpb).le
  have haT : a < T := hap.trans hp.2
  obtain ⟨delta, hdelta, H, hmap, _, _, hcollar⟩ :=
    m64Intrinsic_exists_positive_loop_collar hg hend hinj hab ha hb
      (fun t ht => hregular t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩)
      hU hfront (hray a ⟨ha, haT⟩)
  have hpab : p ∈ Icc a b := ⟨hap.le, hpb.le⟩
  have hps : (p, (0 : ℝ)) ∈ H.source := (hcollar p hpab 0 ⟨le_rfl, hdelta.le⟩).1
  have hbase : H (p, 0) = gamma p := by rw [hmap, normalStrip_axis]
  have hpt : gamma p ∈ H.target := hbase ▸ H.map_source hps
  have hinverse : H.symm (gamma p) = (p, 0) := by rw [← hbase, H.left_inv hps]
  obtain ⟨L, hL, hd⟩ := exists_strictFDerivAt_normalStrip_axis hg (hregular p hp)
  have hHfun : (H : (ℝ × ℝ) → AnnulusCoordinates) = normalStrip gamma := funext hmap
  have hHd : HasFDerivAt H (L : (ℝ × ℝ) →L[ℝ] AnnulusCoordinates) (p, 0) := by
    rw [hHfun]
    exact hd.hasFDerivAt
  have hdi : HasFDerivAt H.symm (L.symm : AnnulusCoordinates →L[ℝ] (ℝ × ℝ))
      (gamma p) := H.hasFDerivAt_symm hpt (hinverse ▸ hHd)
  have hrayderiv : HasDerivAt (fun r : ℝ => gamma p + r • w) w 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (gamma p)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const w) using 1
    simp
  have hdi' : HasFDerivAt H.symm (L.symm : AnnulusCoordinates →L[ℝ] (ℝ × ℝ))
      (gamma p + (0 : ℝ) • w) := by simpa only [zero_smul, add_zero] using hdi
  have hpath : HasDerivAt (fun r : ℝ => H.symm (gamma p + r • w)) (L.symm w) 0 := by
    convert! hdi'.comp_hasDerivAt 0 hrayderiv using 1
  have hnormal : quarterTurn (deriv gamma p) ≠ 0 := by
    intro hn
    simp only [hn, inner_zero_left] at hw
    exact (lt_irrefl 0) hw
  have hheight : 0 < (L.symm w).2 := by
    have horth : inner ℝ (quarterTurn (deriv gamma p)) (deriv gamma p) = 0 := by
      rw [real_inner_comm]
      exact inner_quarterTurn_self _
    have heq := congrArg (fun z => inner ℝ (quarterTurn (deriv gamma p)) z)
      (hL (L.symm w))
    rw [L.apply_symm_apply, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, horth, mul_zero, zero_add] at heq
    exact (mul_pos_iff_of_pos_right (real_inner_self_pos.mpr hnormal)).mp (heq ▸ hw)
  have hheightderiv : HasDerivAt (fun r : ℝ => (H.symm (gamma p + r • w)).2)
      (L.symm w).2 0 := by
    convert! hasFDerivAt_snd.comp_hasDerivAt 0 hpath using 1
  have hheightzero : (H.symm (gamma p + (0 : ℝ) • w)).2 = 0 := by
    simp only [zero_smul, add_zero, hinverse]
  have hpos := eventually_positive_of_derivative hheightderiv hheightzero hheight
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ),
      H.symm (gamma p + r • w) ∈ Ioo a b ×ˢ Ioo (-delta) delta := by
    have hlim : Tendsto (fun r : ℝ => H.symm (gamma p + r • w)) (𝓝 0) (𝓝 (p, 0)) := by
      simpa only [zero_smul, add_zero, hinverse] using hpath.continuousAt.tendsto
    have hnhds : Ioo a b ×ˢ Ioo (-delta) delta ∈ 𝓝 (p, (0 : ℝ)) :=
      (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨⟨hap, hpb⟩, ⟨by linarith, hdelta⟩⟩
    exact hlim.eventually hnhds
  have htarget : ∀ᶠ r in 𝓝 (0 : ℝ), gamma p + r • w ∈ H.target :=
    hrayderiv.continuousAt.preimage_mem_nhds (by
      simpa only [zero_smul, add_zero] using H.open_target.mem_nhds hpt)
  filter_upwards [hpos, hnear.filter_mono nhdsWithin_le_nhds,
    htarget.filter_mono nhdsWithin_le_nhds] with r hrpos hrnear hrtarget
  have h := (hcollar (H.symm (gamma p + r • w)).1 ⟨hrnear.1.1.le, hrnear.1.2.le⟩
    (H.symm (gamma p + r • w)).2 ⟨hrpos.le, hrnear.2.2.le⟩).2.2 hrpos
  simpa only [Prod.eta, H.right_inv hrtarget] using h

end PoincareConjecture
