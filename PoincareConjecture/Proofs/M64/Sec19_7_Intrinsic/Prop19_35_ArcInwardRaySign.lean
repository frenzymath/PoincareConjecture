import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcNormalNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InwardRaySign













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem arc_positive_normal_germ
    {gamma : ℝ → AnnulusCoordinates} {p : ℝ}
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hf : frontier U = frontier V)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hps : (p, (0 : ℝ)) ∈ H.source) (hmap : ∀ q, H q = normalStrip gamma q)
    (hline : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • quarterTurn (deriv gamma p) ∈ U) :
    ∀ᶠ q in 𝓝 (p, (0 : ℝ)), H q ∈ closure U ↔ 0 ≤ q.2 := by
  have hfront : H (p, 0) ∈ frontier U := (hline _ hps).mpr rfl
  have hline' : ∀ᶠ q in 𝓝 (p, (0 : ℝ)), H q ∈ frontier U ↔ q.2 = 0 := by
    filter_upwards [H.open_source.mem_nhds hps] with q hq using hline q hq
  rcases m64Intrinsic_jordan_product_line_germ hU hV hdisj hf H hps hfront hline'
      with hpos | hneg
  · exact hpos
  · have hpath : Tendsto (fun r : ℝ => (p, r)) (𝓝 0) (𝓝 (p, (0 : ℝ))) :=
      continuous_const.prodMk continuous_id |>.tendsto 0
    have hneg' : ∀ᶠ r in 𝓝[>] (0 : ℝ), H (p, r) ∈ closure U ↔ r ≤ 0 :=
      (hpath.eventually hneg).filter_mono nhdsWithin_le_nhds
    have hfalse : ∀ᶠ r in 𝓝[>] (0 : ℝ), False := by
      filter_upwards [hray, hneg', self_mem_nhdsWithin] with r hrU hrside hrpos
      have hcl : H (p, r) ∈ closure U := by
        simpa only [hmap, normalStrip] using subset_closure hrU
      exact (show 0 < r from hrpos).not_ge (hrside.mp hcl)
    obtain ⟨_, h⟩ := hfalse.exists
    exact False.elim h





theorem m64Intrinsic_arc_inward_ray_transverse_pos
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B p : ℝ}
    (hinj : InjOn gamma (Icc A B)) (hp : p ∈ Ioo A B)
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : gamma p ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc A B ∪ K) (hfV : frontier V = frontier U)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • quarterTurn (deriv gamma p) ∈ U)
    {w : AnnulusCoordinates} (hw : inner ℝ (quarterTurn (deriv gamma p)) w ≠ 0)
    (hwray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • w ∈ closure U) :
    0 < inner ℝ (quarterTurn (deriv gamma p)) w := by
  obtain ⟨delta, hdelta, H, hsource, hmap, _, _, hboundary⟩ :=
    m64Intrinsic_exists_arc_normal_neighborhood hg hinj le_rfl hp.1 hp.2 hregular hK
      (fun t ht => by have he : t = p := le_antisymm ht.2 ht.1; simpa only [he] using hpK)
  have hline : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0 := by
    simpa only [hfU] using hboundary
  have hps : (p, (0 : ℝ)) ∈ H.source := hsource ⟨by simp, ⟨by linarith, hdelta⟩⟩
  have hbase : H (p, 0) = gamma p := by rw [hmap, normalStrip_axis]
  have hpt : gamma p ∈ H.target := hbase ▸ H.map_source hps
  have hinverse : H.symm (gamma p) = (p, 0) := by rw [← hbase, H.left_inv hps]
  have hside := arc_positive_normal_germ hU hV hdisj hfV.symm H hps hmap hline hray
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





theorem m64Intrinsic_arc_transverse_ray_enters_region
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {A B p : ℝ}
    (hinj : InjOn gamma (Icc A B)) (hp : p ∈ Ioo A B)
    (hregular : ∀ t ∈ Ioo A B, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : gamma p ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc A B ∪ K) (hfV : frontier V = frontier U)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • quarterTurn (deriv gamma p) ∈ U)
    {w : AnnulusCoordinates} (hw : 0 < inner ℝ (quarterTurn (deriv gamma p)) w) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma p + r • w ∈ U := by
  obtain ⟨delta, hdelta, H, hsource, hmap, _, _, hboundary⟩ :=
    m64Intrinsic_exists_arc_normal_neighborhood hg hinj le_rfl hp.1 hp.2 hregular hK
      (fun t ht => by have he : t = p := le_antisymm ht.2 ht.1; simpa only [he] using hpK)
  have hline : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0 := by
    simpa only [hfU] using hboundary
  have hps : (p, (0 : ℝ)) ∈ H.source := hsource ⟨by simp, ⟨by linarith, hdelta⟩⟩
  have hbase : H (p, 0) = gamma p := by rw [hmap, normalStrip_axis]
  have hpt : gamma p ∈ H.target := hbase ▸ H.map_source hps
  have hinverse : H.symm (gamma p) = (p, 0) := by rw [← hbase, H.left_inv hps]
  have hside := arc_positive_normal_germ hU hV hdisj hfV.symm H hps hmap hline hray
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
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < (H.symm (gamma p + r • w)).2 := by
    have hs := hheightderiv.tendsto_slope_zero_right.eventually_const_lt hheight
    filter_upwards [hs, self_mem_nhdsWithin] with r hr hrpos
    have hrpos' : 0 < r := hrpos
    simp only [zero_add, zero_smul, add_zero, hinverse, sub_zero, smul_eq_mul] at hr
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hrpos')).mp hr
  have hlim : Tendsto (fun r : ℝ => H.symm (gamma p + r • w)) (𝓝 0) (𝓝 (p, 0)) := by
    simpa only [zero_smul, add_zero, hinverse] using hpath.continuousAt.tendsto
  have htarget : ∀ᶠ r in 𝓝 (0 : ℝ), gamma p + r • w ∈ H.target :=
    hrayderiv.continuousAt.preimage_mem_nhds (by
      simpa only [zero_smul, add_zero] using H.open_target.mem_nhds hpt)
  filter_upwards [hpos, (hlim.eventually hside).filter_mono nhdsWithin_le_nhds,
    htarget.filter_mono nhdsWithin_le_nhds] with r hrpos hrside hrtarget
  have hcl : gamma p + r • w ∈ closure U := by
    have h := hrside.mpr hrpos.le
    rwa [H.right_inv hrtarget] at h
  by_contra hn
  have hfront : gamma p + r • w ∈ frontier U :=
    ⟨hcl, by simpa only [hU.interior_eq] using hn⟩
  have hzero := (hline _ (H.map_target hrtarget)).mp
    (by simpa only [H.right_inv hrtarget] using hfront)
  exact hrpos.ne' hzero

end PoincareConjecture
