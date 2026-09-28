import PoincareConjecture.Proofs.M25.Mathlib.PositiveRadialPrimitive
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Order.IntermediateValue












set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Real

variable {f : ℝ → ℝ} {L l m u U b : ℝ}




theorem tendsto_positiveRadialPrimitive_anchor (hLl : L < l) (hmu : m < u)
    (huU : u < U) (hlb : l < b) (hf : ContDiffOn ℝ ∞ f (Ioo L U)) :
    Tendsto (positiveRadialPrimitive f l m u b) (𝓝[>] l) (𝓝 (f l)) := by
  have hc := ((contDiffOn_positiveRadialPrimitive hmu huU hf ⟨hLl, hlb⟩).contDiffAt
    (isOpen_Ioo.mem_nhds ⟨hLl, hlb⟩)).continuousAt
  simpa only [positiveRadialPrimitive_apply_anchor] using hc.tendsto.mono_left nhdsWithin_le_nhds




theorem tendsto_positiveRadialPrimitive_atTop (hLl : L < l) (hlm : l < m)
    (hmu : m < u) (huU : u < U) (hub : u < b)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U)) :
    Tendsto (positiveRadialPrimitive f l m u b) (𝓝[<] b) atTop := by
  have hzero : Tendsto (fun s : ℝ => b - s) (𝓝[<] b) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hid : Tendsto (fun s : ℝ => s) (𝓝[<] b) (𝓝 b) :=
        tendsto_id'.mpr nhdsWithin_le_nhds
      simpa only [sub_self] using (tendsto_const_nhds.sub hid :
        Tendsto (fun s : ℝ => b - s) (𝓝[<] b) (𝓝 (b - b)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 0 < b - s
      exact sub_pos.mpr hs
  have hlim := tendsto_atTop_add_const_left (𝓝[<] b)
    (positiveRadialPrimitive f l m u b u - (b - u)⁻¹)
    hzero.inv_tendsto_nhdsGT_zero
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds hub)] with s hsb hus
  rw [positiveRadialPrimitive_upper_formula hLl hlm hmu huU hub hf ⟨hus.le, hsb⟩]
  simp only [Pi.inv_apply]
  ring




theorem image_positiveRadialPrimitive_Ioo (hLl : L < l) (hlm : l < m)
    (hmu : m < u) (huU : u < U) (hub : u < b)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U))
    (hfderiv : ∀ s ∈ Icc l u, 0 < deriv f s) :
    positiveRadialPrimitive f l m u b '' Ioo l b = Ioi (f l) := by
  have hlb : l < b := ((hlm.trans hmu).trans hub)
  have hmono := strictMonoOn_positiveRadialPrimitive hLl hmu huU hlb hf hfderiv
  have hcont := (contDiffOn_positiveRadialPrimitive hmu huU hf ⟨hLl, hlb⟩).continuousOn
  have hlim := tendsto_positiveRadialPrimitive_atTop hLl hlm hmu huU hub hf
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hlt := hmono (show l ∈ Ico l b from ⟨le_rfl, hlb⟩)
      ⟨hs.1.le, hs.2⟩ hs.1
    simpa only [mem_Ioi, positiveRadialPrimitive_apply_anchor] using hlt
  · intro hy
    have hev : ∀ᶠ v in 𝓝[<] b, l < v ∧ v < b ∧ y < positiveRadialPrimitive f l m u b v := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hlb),
        self_mem_nhdsWithin, hlim.eventually_gt_atTop y] with v hlv hvb hyR
      exact ⟨hlv, hvb, hyR⟩
    obtain ⟨v, hlv, hvb, hyv⟩ := hev.exists
    have hcont' := hcont.mono (show Icc l v ⊆ Ioo L b from
      fun s hs => ⟨hLl.trans_le hs.1, hs.2.trans_lt hvb⟩)
    have hy' : y ∈ Ioo (positiveRadialPrimitive f l m u b l)
        (positiveRadialPrimitive f l m u b v) := by
      rw [positiveRadialPrimitive_apply_anchor]
      exact ⟨hy, hyv⟩
    obtain ⟨s, hs, hsy⟩ := intermediate_value_Ioo hlv.le hcont' hy'
    exact ⟨s, ⟨hs.1, hs.2.trans hvb⟩, hsy⟩






theorem exists_positive_radial_extension (hLl : L < l) (hlm : l < m)
    (hmu : m < u) (huU : u < U) (hub : u < b)
    (hf : ContDiffOn ℝ ∞ f (Ioo L U))
    (hfderiv : ∀ s ∈ Icc l u, 0 < deriv f s) (hfpos : 0 < f l) :
    ∃ rho : OpenPartialHomeomorph ℝ ℝ,
      rho.source = Ioo l b ∧ rho.target = Ioi (f l) ∧
      ContDiffOn ℝ ∞ (rho : ℝ → ℝ) (Ioo L b) ∧
      ContDiffOn ℝ ∞ rho.symm rho.target ∧
      EqOn (rho : ℝ → ℝ) f (Icc l m) ∧
      StrictMonoOn (rho : ℝ → ℝ) (Ico l b) ∧
      (∀ s ∈ Ico l b, 0 < rho s) ∧
      (∀ s ∈ Ico l b, 0 < deriv (rho : ℝ → ℝ) s) ∧
      Tendsto (rho : ℝ → ℝ) (𝓝[<] b) atTop := by
  classical
  let R := positiveRadialPrimitive f l m u b
  have hlb : l < b := ((hlm.trans hmu).trans hub)
  have hsub : Ioo l b ⊆ Ioo L b := fun _ hs => ⟨hLl.trans hs.1, hs.2⟩
  have hR : ContDiffOn ℝ ∞ R (Ioo L b) :=
    contDiffOn_positiveRadialPrimitive hmu huU hf ⟨hLl, hlb⟩
  have hmono : StrictMonoOn R (Ico l b) :=
    strictMonoOn_positiveRadialPrimitive hLl hmu huU hlb hf hfderiv
  have hmono' : StrictMonoOn R (Ioo l b) := hmono.mono Ioo_subset_Ico_self
  have himage : R '' Ioo l b = Ioi (f l) :=
    image_positiveRadialPrimitive_Ioo hLl hlm hmu huU hub hf hfderiv
  have hstrict : StrictMono ((Ioo l b).domRestrict R) :=
    fun x y hxy => hmono' x.property y.property hxy
  have hrange : range ((Ioo l b).domRestrict R) = Ioi (f l) := by
    rw [range_domRestrict, himage]
  have hemb := hstrict.isEmbedding_of_ordConnected (by rw [hrange]; infer_instance)
  have hopen : Topology.IsOpenEmbedding ((Ioo l b).domRestrict R) :=
    ⟨hemb, by rw [hrange]; exact isOpen_Ioi⟩
  let pe := Set.InjOn.toPartialEquiv R (Ioo l b) hmono'.injOn
  let rho := OpenPartialHomeomorph.ofContinuousOpenRestrict pe
    (hR.continuousOn.mono hsub) hopen.isOpenMap isOpen_Ioo
  have hi : ContDiffOn ℝ ∞ rho.symm rho.target := by
    intro y hy
    have hx : rho.symm y ∈ Ioo l b := rho.map_target hy
    have hF : ContDiffAt ℝ ∞ (rho : ℝ → ℝ) (rho.symm y) :=
      hR.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))
    have hd : 0 < deriv (rho : ℝ → ℝ) (rho.symm y) :=
      deriv_positiveRadialPrimitive_pos hLl hmu huU hlb hf hfderiv ⟨hx.1.le, hx.2⟩
    exact (rho.contDiffAt_symm_deriv hd.ne' hy
      (hF.differentiableAt (by simp)).hasDerivAt hF).contDiffWithinAt
  exact ⟨rho, rfl, himage, hR, hi, positiveRadialPrimitive_eqOn hLl hmu huU hf,
    hmono, fun s hs => positiveRadialPrimitive_pos hLl hmu huU hlb hf hfderiv hfpos hs,
    fun s hs => deriv_positiveRadialPrimitive_pos hLl hmu huU hlb hf hfderiv hs,
    tendsto_positiveRadialPrimitive_atTop hLl hlm hmu huU hub hf⟩

end Real

namespace OpenPartialHomeomorph

variable (rho : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ} {l m b v : ℝ}




theorem image_Ioo_and_symm_of_eqOn_Icc (hlm : l ≤ m)
    (hsub : Ioo l m ⊆ rho.source) (hcont : ContinuousOn rho (Icc l m))
    (hmono : StrictMonoOn rho (Icc l m)) (heq : EqOn (rho : ℝ → ℝ) f (Icc l m)) :
    rho '' Ioo l m = Ioo (f l) (f m) ∧
      ∀ y ∈ Ioo (f l) (f m), rho.symm y ∈ Ioo l m ∧ f (rho.symm y) = y := by
  have himage := hcont.image_Ioo_of_strictMonoOn hlm hmono
  rw [heq ⟨le_rfl, hlm⟩, heq ⟨hlm, le_rfl⟩] at himage
  refine ⟨himage, ?_⟩
  intro y hy
  obtain ⟨s, hs, hsy⟩ := himage.symm ▸ hy
  have hi : rho.symm y = s := by rw [← hsy, rho.left_inv (hsub hs)]
  rw [hi]
  exact ⟨hs, (heq ⟨hs.1.le, hs.2.le⟩).symm.trans hsy⟩





theorem exists_smooth_radial_restriction
    (hsource : rho.source = Ioo l b) (htarget : rho.target = Ioi (rho l))
    (hf : ContDiffOn ℝ ∞ (rho : ℝ → ℝ) rho.source)
    (hi : ContDiffOn ℝ ∞ rho.symm rho.target)
    (hmono : StrictMonoOn (rho : ℝ → ℝ) (Ico l b))
    (hpos : ∀ s ∈ Ico l b, 0 < rho s)
    (hderiv : ∀ s ∈ rho.source, 0 < deriv (rho : ℝ → ℝ) s) (hv : v ∈ Ico l b) :
    ∃ sigma : OpenPartialHomeomorph ℝ ℝ,
      sigma.source = Ioo v b ∧ sigma.target = Ioi (rho v) ∧
      (sigma : ℝ → ℝ) = rho ∧ (sigma.symm : ℝ → ℝ) = rho.symm ∧
      0 < rho v ∧ ContDiffOn ℝ ∞ (sigma : ℝ → ℝ) sigma.source ∧
      ContDiffOn ℝ ∞ sigma.symm sigma.target ∧
      StrictMonoOn (sigma : ℝ → ℝ) sigma.source ∧
      (∀ s ∈ sigma.source, 0 < deriv (sigma : ℝ → ℝ) s) := by
  have hsrcsub : Ioo v b ⊆ rho.source := by
    rw [hsource]
    exact fun _ hs => ⟨hv.1.trans_lt hs.1, hs.2⟩
  have htarsub : Ioi (rho v) ⊆ rho.target := by
    rw [htarget]
    intro y hy
    exact (hmono.monotoneOn ⟨le_rfl, hv.1.trans_lt hv.2⟩ hv hv.1).trans_lt hy
  have himage : rho.IsImage (Ioo v b) (Ioi (rho v)) := by
    intro s hs
    have hs' : s ∈ Ioo l b := hsource ▸ hs
    change rho v < rho s ↔ v < s ∧ s < b
    rw [hmono.lt_iff_lt hv ⟨hs'.1.le, hs'.2⟩]
    exact ⟨fun h => ⟨h, hs'.2⟩, And.left⟩
  let sigma := himage.restr (rho.open_source.inter isOpen_Ioo)
  have hsigma : sigma.source = Ioo v b := inter_eq_right.mpr hsrcsub
  have htarget_sigma : sigma.target = Ioi (rho v) := inter_eq_right.mpr htarsub
  have hsco : sigma.source ⊆ Ico l b := by
    intro s hs
    have hs' : s ∈ Ioo l b := hsource ▸ hs.1
    exact ⟨hs'.1.le, hs'.2⟩
  exact ⟨sigma, hsigma, htarget_sigma, rfl, rfl, hpos v hv,
    hf.mono inter_subset_left, hi.mono inter_subset_left, hmono.mono hsco,
    fun s hs => hderiv s hs.1⟩

end OpenPartialHomeomorph
