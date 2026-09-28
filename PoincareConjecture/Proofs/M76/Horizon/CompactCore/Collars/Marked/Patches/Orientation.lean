import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.PlanarSides

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)

theorem exists_partial_planar_strip_orientation
    {w a b : ℝ} (hw : 0 < w) (hab : a < b) {g : P2 → P2}
    (hg : FinitePiecewiseAffineOn g (Icc (-w) w ×ˢ Icc a b))
    (hi : InjOn g (Icc (-w) w ×ˢ Icc a b))
    (hcenter : ∀ t ∈ Icc a b, g (0, t) = (t, 0))
    (hzero : ∀ p ∈ Icc (-w) w ×ˢ Icc a b, (g p).2 = 0 ↔ p.1 = 0) :
    ∃ o : Bool,
      (∀ p ∈ Ioc (0 : ℝ) w ×ˢ Icc a b, 0 < TubeExterior.CornerBands.sign o * (g p).2) ∧
      (∀ p ∈ Ico (-w) 0 ×ˢ Icc a b, TubeExterior.CornerBands.sign o * (g p).2 < 0) := by
  have hp : Ioc (0 : ℝ) w ×ˢ Icc a b ⊆ Icc (-w) w ×ˢ Icc a b := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], hp.1.2⟩, hp.2⟩
  have hn : Ico (-w) 0 ×ˢ Icc a b ⊆ Icc (-w) w ×ˢ Icc a b := by
    intro p hp
    exact ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩
  have hheight : ContinuousOn (fun p => (g p).2) (Icc (-w) w ×ˢ Icc a b) :=
    continuous_snd.comp_continuousOn hg.continuousOn
  have hpos := (isPreconnected_Ioc.prod isPreconnected_Icc).mapsTo_Ioi_or_Iio
    (hheight.mono hp) (fun p h h0 => (ne_of_gt h.1.1) ((hzero p (hp h)).mp h0))
  have hneg := (isPreconnected_Ico.prod isPreconnected_Icc).mapsTo_Ioi_or_Iio
    (hheight.mono hn) (fun p h h0 => (ne_of_lt h.1.2) ((hzero p (hn h)).mp h0))
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hmid : (0, m) ∈ interior (Icc (-w) w ×ˢ Icc a b) := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨neg_neg_of_pos hw, hw⟩, hm⟩
  have himid := hg.mem_interior_image rfl hi hmid
  rw [hcenter m (Ioo_subset_Icc_self hm)] at himid
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ himid
  have hex (s : ℝ) (hs : |s| < r) :
      ∃ p ∈ Icc (-w) w ×ˢ Icc a b, (g p).2 = s := by
    have hnear : (m, s) ∈ ball (m, (0 : ℝ)) r := by
      simpa only [mem_ball, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
        sub_zero, max_eq_right (abs_nonneg s)] using hs
    obtain ⟨p, hp', hv⟩ := interior_subset (hball hnear)
    exact ⟨p, hp', congrArg Prod.snd hv⟩
  obtain ⟨p, hp', hpheight⟩ := hex (r / 2)
    (by rw [abs_of_pos (half_pos hr)]; exact half_lt_self hr)
  obtain ⟨q, hq', hqheight⟩ := hex (-(r / 2))
    (by rw [abs_neg, abs_of_pos (half_pos hr)]; exact half_lt_self hr)
  have hpv : 0 < (g p).2 := hpheight.symm ▸ half_pos hr
  have hqv : (g q).2 < 0 := hqheight.symm ▸ neg_neg_of_pos (half_pos hr)
  have hpn : p.1 ≠ 0 := fun h => (ne_of_gt hpv) ((hzero p hp').mpr h)
  have hqn : q.1 ≠ 0 := fun h => (ne_of_lt hqv) ((hzero q hq').mpr h)
  rcases hpos with hpos | hpos <;> rcases hneg with hneg | hneg
  · exfalso
    rcases lt_or_gt_of_ne hqn with hq | hq
    · exact (not_lt_of_ge hqv.le) (hneg ⟨⟨hq'.1.1, hq⟩, hq'.2⟩)
    · exact (not_lt_of_ge hqv.le) (hpos ⟨⟨hq, hq'.1.2⟩, hq'.2⟩)
  · exact ⟨false, fun _ h => by simpa [TubeExterior.CornerBands.sign] using hpos h,
      fun _ h => by simpa [TubeExterior.CornerBands.sign] using hneg h⟩
  · exact ⟨true, fun _ h => by simpa [TubeExterior.CornerBands.sign] using hpos h,
      fun _ h => by simpa [TubeExterior.CornerBands.sign] using hneg h⟩
  · exfalso
    rcases lt_or_gt_of_ne hpn with hp | hp
    · exact (not_lt_of_ge hpv.le) (hneg ⟨⟨hp'.1.1, hp⟩, hp'.2⟩)
    · exact (not_lt_of_ge hpv.le) (hpos ⟨⟨hp, hp'.1.2⟩, hp'.2⟩)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
