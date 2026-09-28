import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseInwardRay

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem positive_normal_germ
    {gamma : ℝ → AnnulusCoordinates} {T p : ℝ}
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) (hp : p ∈ Icc (0 : ℝ) T)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hps : (p, (0 : ℝ)) ∈ H.source) (hmap : ∀ q, H q = normalStrip gamma q)
    (hline : ∀ q ∈ H.source, H q ∈ gamma '' Icc 0 T ↔ q.2 = 0)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • quarterTurn (deriv gamma p) ∈ U) :
    ∀ᶠ q in 𝓝 (p, (0 : ℝ)), H q ∈ closure U ↔ 0 ≤ q.2 := by
  have hfront : H (p, 0) ∈ frontier U := by
    rw [hmap, normalStrip_axis, hfU]
    exact ⟨p, hp, rfl⟩
  have hline' : ∀ᶠ q in 𝓝 (p, (0 : ℝ)), H q ∈ frontier U ↔ q.2 = 0 := by
    filter_upwards [H.open_source.mem_nhds hps] with q hq
    simpa only [hfU] using hline q hq
  rcases m64Intrinsic_jordan_product_line_germ hU hV hdisj (hfU.trans hfV.symm)
    H hps hfront hline' with hpos | hneg
  · exact hpos
  · have hpath : Tendsto (fun r : ℝ => (p, r)) (𝓝 0) (𝓝 (p, (0 : ℝ))) :=
      continuous_const.prodMk continuous_id |>.tendsto 0
    have hneg' : ∀ᶠ r in 𝓝[>] (0 : ℝ), H (p, r) ∈ closure U ↔ r ≤ 0 :=
      (hpath.eventually hneg).filter_mono nhdsWithin_le_nhds
    have hfalse : ∀ᶠ r in 𝓝[>] (0 : ℝ), False := by
      filter_upwards [hray, hneg', self_mem_nhdsWithin] with r hrU hrside hrpos
      have hrpos' : 0 < r := hrpos
      have hcl : H (p, r) ∈ closure U := by
        simpa only [hmap, normalStrip] using subset_closure hrU
      exact hrpos'.not_ge (hrside.mp hcl)
    obtain ⟨_, h⟩ := hfalse.exists
    exact False.elim h

theorem m64Intrinsic_inward_ray_transverse_pos
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • quarterTurn (deriv gamma p) ∈ U)
    {w : AnnulusCoordinates}
    (hw : inner ℝ (quarterTurn (deriv gamma p)) w ≠ 0)
    (hwray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • w ∈ closure U) :
    0 < inner ℝ (quarterTurn (deriv gamma p)) w := by
  have hreg : ∀ t ∈ Icc p p, deriv gamma t ≠ 0 := by
    intro t ht
    have he : t = p := le_antisymm ht.2 ht.1
    simpa only [he] using hregular
  obtain ⟨delta, hdelta, H, hsource, hmap, _, _, hline⟩ :=
    m64Intrinsic_exists_loop_normal_neighborhood hg hend hinj le_rfl hp.1 hp.2 hreg
  have hps : (p, (0 : ℝ)) ∈ H.source := hsource ⟨by simp, ⟨by linarith, hdelta⟩⟩
  have hbase : H (p, 0) = gamma p := by rw [hmap, normalStrip_axis]
  have hpt : gamma p ∈ H.target := hbase ▸ H.map_source hps
  have hinverse : H.symm (gamma p) = (p, 0) := by rw [← hbase, H.left_inv hps]
  have hside := positive_normal_germ hU hV hdisj hfU hfV ⟨hp.1.le, hp.2.le⟩
    H hps hmap hline hray
  obtain ⟨L, hL, hd⟩ := exists_strictFDerivAt_normalStrip_axis hg hregular
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
  have hheightderiv : HasDerivAt (fun r : ℝ => (H.symm (gamma p + r • w)).2)
      (L.symm w).2 0 := by
    convert! hasFDerivAt_snd.comp_hasDerivAt 0 hpath using 1
  have hlim : Tendsto (fun r : ℝ => H.symm (gamma p + r • w)) (𝓝 0) (𝓝 (p, 0)) := by
    simpa only [zero_smul, add_zero, hinverse] using hpath.continuousAt.tendsto
  have htarget : ∀ᶠ r in 𝓝 (0 : ℝ), gamma p + r • w ∈ H.target :=
    hrayderiv.continuousAt.preimage_mem_nhds (by
      simpa only [zero_smul, add_zero] using H.open_target.mem_nhds hpt)
  have hheightnonneg : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 ≤ (H.symm (gamma p + r • w)).2 := by
    filter_upwards [hwray, (hlim.eventually hside).filter_mono nhdsWithin_le_nhds,
      htarget.filter_mono nhdsWithin_le_nhds] with r hr hrside hrtarget
    apply hrside.mp
    rwa [H.right_inv hrtarget]
  have hnonneg : 0 ≤ (L.symm w).2 := by
    apply ge_of_tendsto hheightderiv.tendsto_slope_zero_right
    filter_upwards [hheightnonneg, self_mem_nhdsWithin] with r hr hrpos
    have hrpos' : 0 < r := hrpos
    simpa only [zero_add, zero_smul, add_zero, hinverse, sub_zero, smul_eq_mul] using
      mul_nonneg (inv_nonneg.mpr hrpos'.le) hr
  have horth : inner ℝ (quarterTurn (deriv gamma p)) (deriv gamma p) = 0 := by
    rw [real_inner_comm]
    exact inner_quarterTurn_self _
  have heq := congrArg (fun z => inner ℝ (quarterTurn (deriv gamma p)) z) (hL (L.symm w))
  rw [L.apply_symm_apply, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    horth, mul_zero, zero_add] at heq
  have hnonneg' : 0 ≤ inner ℝ (quarterTurn (deriv gamma p)) w := by
    rw [heq]
    exact mul_nonneg hnonneg real_inner_self_nonneg
  exact lt_of_le_of_ne hnonneg' (Ne.symm hw)

end PoincareConjecture
