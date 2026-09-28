import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLLocalInterior
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.Coordinates







set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem planar_strip_opposite_sides
    {w : ℝ} (hw : 0 < w) {g : P2 → P2}
    (hg : FinitePiecewiseAffineOn g (Icc (-w) w ×ˢ I))
    (hi : InjOn g (Icc (-w) w ×ˢ I))
    (hcenter : ∀ t ∈ I, g (0,t) = (t,0))
    (hzero : ∀ p ∈ Icc (-w) w ×ˢ I, (g p).2 = 0 ↔ p.1 = 0) :
    ((∀ p ∈ Ioc (0 : ℝ) w ×ˢ I, 0 < (g p).2) ∧
      (∀ p ∈ Ico (-w) 0 ×ˢ I, (g p).2 < 0)) ∨
    ((∀ p ∈ Ioc (0 : ℝ) w ×ˢ I, (g p).2 < 0) ∧
      (∀ p ∈ Ico (-w) 0 ×ˢ I, 0 < (g p).2)) := by
  have hp : Ioc (0 : ℝ) w ×ˢ I ⊆ Icc (-w) w ×ˢ I := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], hp.1.2⟩, hp.2⟩
  have hn : Ico (-w) 0 ×ˢ I ⊆ Icc (-w) w ×ˢ I := by
    intro p hp
    exact ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩
  have hheight : ContinuousOn (fun p ↦ (g p).2) (Icc (-w) w ×ˢ I) :=
    continuous_snd.comp_continuousOn hg.continuousOn
  have hpos := (isPreconnected_Ioc.prod isPreconnected_Icc).mapsTo_Ioi_or_Iio
    (hheight.mono hp) (fun p hp' h ↦ (ne_of_gt hp'.1.1) ((hzero p (hp hp')).mp h))
  have hneg := (isPreconnected_Ico.prod isPreconnected_Icc).mapsTo_Ioi_or_Iio
    (hheight.mono hn) (fun p hp' h ↦ (ne_of_lt hp'.1.2) ((hzero p (hn hp')).mp h))
  have hmid : (0, (1 / 2 : ℝ)) ∈ interior (Icc (-w) w ×ˢ I) := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    constructor
    · exact ⟨neg_neg_of_pos hw, hw⟩
    · norm_num
  have himid := hg.mem_interior_image rfl hi hmid
  rw [hcenter (1 / 2) (by norm_num)] at himid
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ himid
  have hex (s : ℝ) (hs : |s| < r) :
      ∃ p ∈ Icc (-w) w ×ˢ I, (g p).2 = s := by
    have hnear : ((1 / 2 : ℝ), s) ∈ ball ((1 / 2 : ℝ), 0) r := by
      simpa only [mem_ball, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
        sub_zero, max_eq_right (abs_nonneg s)] using hs
    obtain ⟨p, hp', hv⟩ := interior_subset (hball hnear)
    exact ⟨p, hp', congrArg Prod.snd hv⟩
  obtain ⟨p, hp', hpheight⟩ := hex (r / 2) (by rw [abs_of_pos (half_pos hr)]; exact half_lt_self hr)
  obtain ⟨q, hq', hqheight⟩ := hex (-(r / 2)) (by
    rw [abs_neg, abs_of_pos (half_pos hr)]
    exact half_lt_self hr)
  have hpv : 0 < (g p).2 := hpheight.symm ▸ half_pos hr
  have hqv : (g q).2 < 0 := hqheight.symm ▸ neg_neg_of_pos (half_pos hr)
  have hpn : p.1 ≠ 0 := fun hh ↦ (ne_of_gt hpv) ((hzero p hp').mpr hh)
  have hqn : q.1 ≠ 0 := fun hh ↦ (ne_of_lt hqv) ((hzero q hq').mpr hh)
  rcases hpos with hpos | hpos <;> rcases hneg with hneg | hneg
  · exfalso
    rcases lt_or_gt_of_ne hqn with hq | hq
    · exact (not_lt_of_ge hqv.le) (hneg ⟨⟨hq'.1.1, hq⟩, hq'.2⟩)
    · exact (not_lt_of_ge hqv.le) (hpos ⟨⟨hq, hq'.1.2⟩, hq'.2⟩)
  · exact Or.inl ⟨fun _ hp' ↦ hpos hp', fun _ hp' ↦ hneg hp'⟩
  · exact Or.inr ⟨fun _ hp' ↦ hpos hp', fun _ hp' ↦ hneg hp'⟩
  · exfalso
    rcases lt_or_gt_of_ne hpn with hp | hp
    · exact (not_lt_of_ge hpv.le) (hneg ⟨⟨hp'.1.1, hp⟩, hp'.2⟩)
    · exact (not_lt_of_ge hpv.le) (hpos ⟨⟨hp, hp'.1.2⟩, hp'.2⟩)

theorem exists_planar_strip_orientation
    {w : ℝ} (hw : 0 < w) {g : P2 → P2}
    (hg : FinitePiecewiseAffineOn g (Icc (-w) w ×ˢ I))
    (hi : InjOn g (Icc (-w) w ×ˢ I))
    (hcenter : ∀ t ∈ I, g (0,t) = (t,0))
    (hzero : ∀ p ∈ Icc (-w) w ×ˢ I, (g p).2 = 0 ↔ p.1 = 0) :
    ∃ b : Bool,
      (∀ p ∈ Ioc (0 : ℝ) w ×ˢ I, 0 < TubeExterior.CornerBands.sign b * (g p).2) ∧
      (∀ p ∈ Ico (-w) 0 ×ˢ I, TubeExterior.CornerBands.sign b * (g p).2 < 0) := by
  rcases planar_strip_opposite_sides hw hg hi hcenter hzero with ⟨hp, hn⟩ | ⟨hp, hn⟩
  · exact ⟨false, by simpa [TubeExterior.CornerBands.sign] using hp,
      by simpa [TubeExterior.CornerBands.sign] using hn⟩
  · exact ⟨true, by simpa [TubeExterior.CornerBands.sign] using hp,
      by simpa [TubeExterior.CornerBands.sign] using hn⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
