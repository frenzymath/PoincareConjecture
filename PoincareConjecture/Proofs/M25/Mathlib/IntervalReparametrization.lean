import PoincareConjecture.Proofs.M25.Mathlib.PositiveRadialExtension
import Mathlib.Topology.OpenPartialHomeomorph.Composition












set_option autoImplicit false

open Set
open scoped ContDiff

namespace Real




theorem exists_smooth_interval_reparametrization
    {a r b c : ℝ} (har : a < r) (hrb : r < b) (hrc : r < c) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = Ioo a b ∧ e.target = Ioo a c ∧
      ContDiffOn ℝ ∞ (e : ℝ → ℝ) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      StrictMonoOn (e : ℝ → ℝ) e.source ∧
      EqOn (e : ℝ → ℝ) id (Ioc a r) ∧
      EqOn (e.symm : ℝ → ℝ) id (Ioc a r) := by
  let u := (r + min b c) / 2
  have hru : r < u := by
    have h := lt_min hrb hrc
    dsimp only [u]
    linarith
  have hub : u < b := by
    have h := min_le_left b c
    dsimp only [u]
    linarith
  have huc : u < c := by
    have h := min_le_right b c
    dsimp only [u]
    linarith
  let f : ℝ → ℝ := fun s => s - a + 1
  have hf : ContDiff ℝ ∞ f := (contDiff_id.sub contDiff_const).add contDiff_const
  have hdf (s : ℝ) : HasDerivAt f 1 s :=
    ((hasDerivAt_id s).sub_const a).add_const 1
  have hd : ∀ s ∈ Icc a u, 0 < deriv f s := by
    intro s _
    rw [(hdf s).deriv]
    norm_num
  have ha1 : a - 1 < a := by linarith
  have hu1 : u < u + 1 := by linarith
  have hfpos : 0 < f a := by simp [f]
  obtain ⟨eb, hbs, hbt, hb, hbi, hbeq, hbmono, _, _, _⟩ :=
    exists_positive_radial_extension ha1 har hru hu1 hub hf.contDiffOn hd hfpos
  obtain ⟨ec, hcs, hct, hc, hci, hceq, hcmono, _, _, _⟩ :=
    exists_positive_radial_extension ha1 har hru hu1 huc hf.contDiffOn hd hfpos
  have hcommon : eb.target = ec.target := hbt.trans hct.symm
  let e := eb.trans' ec.symm hcommon
  have hbsmooth : ContDiffOn ℝ ∞ (eb : ℝ → ℝ) eb.source := by
    apply hb.mono
    rw [hbs]
    exact fun s hs => ⟨ha1.trans hs.1, hs.2⟩
  have hcsmooth : ContDiffOn ℝ ∞ (ec : ℝ → ℝ) ec.source := by
    apply hc.mono
    rw [hcs]
    exact fun s hs => ⟨ha1.trans hs.1, hs.2⟩
  have he : ContDiffOn ℝ ∞ (e : ℝ → ℝ) e.source :=
    hci.comp hbsmooth (fun _ hx => hcommon ▸ eb.map_source hx)
  have hei : ContDiffOn ℝ ∞ e.symm e.target :=
    hbi.comp hcsmooth (fun _ hy => hcommon.symm ▸ ec.map_source hy)
  have hmono : StrictMonoOn (e : ℝ → ℝ) e.source := by
    intro x hx y hy hxy
    have hxb : x ∈ Ioo a b := hbs ▸ hx
    have hyb : y ∈ Ioo a b := hbs ▸ hy
    have hxyb := hbmono ⟨hxb.1.le, hxb.2⟩ ⟨hyb.1.le, hyb.2⟩ hxy
    have hxt : eb x ∈ ec.target := hcommon ▸ eb.map_source hx
    have hyt : eb y ∈ ec.target := hcommon ▸ eb.map_source hy
    have hxc : ec.symm (eb x) ∈ Ioo a c := hcs ▸ ec.map_target hxt
    have hyc : ec.symm (eb y) ∈ Ioo a c := hcs ▸ ec.map_target hyt
    change ec.symm (eb x) < ec.symm (eb y)
    by_contra h
    have hle := hcmono.monotoneOn ⟨hyc.1.le, hyc.2⟩ ⟨hxc.1.le, hxc.2⟩
      (le_of_not_gt h)
    rw [ec.right_inv hyt, ec.right_inv hxt] at hle
    exact (not_le_of_gt hxyb) hle
  refine ⟨e, hbs, hcs, he, hei, hmono, ?_, ?_⟩
  · intro s hs
    change ec.symm (eb s) = s
    rw [hbeq ⟨hs.1.le, hs.2⟩, ← hceq ⟨hs.1.le, hs.2⟩]
    exact ec.left_inv (hcs.symm ▸ ⟨hs.1, hs.2.trans_lt hrc⟩)
  · intro s hs
    change eb.symm (ec s) = s
    rw [hceq ⟨hs.1.le, hs.2⟩, ← hbeq ⟨hs.1.le, hs.2⟩]
    exact eb.left_inv (hbs.symm ▸ ⟨hs.1, hs.2.trans_lt hrb⟩)

end Real
