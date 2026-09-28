import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InwardArcStrips

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem positive_normal_strip_of_ray
    {gamma : ℝ → AnnulusCoordinates} {T a b q : ℝ}
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hfront : frontier U = gamma '' Icc 0 T)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {delta : ℝ}
    (hdelta : 0 < delta)
    (hsource : Icc a b ×ˢ Ioo (-delta) delta ⊆ H.source)
    (hmap : ∀ z, H z = normalStrip gamma z)
    (hline : ∀ z ∈ H.source, H z ∈ gamma '' Icc 0 T ↔ z.2 = 0)
    (hq : q ∈ Icc a b)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma q + r • quarterTurn (deriv gamma q) ∈ U) :
    ∀ t ∈ Icc a b, ∀ r ∈ Ioo (0 : ℝ) delta, H (t, r) ∈ U := by
  let S := Icc a b ×ˢ Ioo (0 : ℝ) delta
  have hS : S ⊆ H.source :=
    fun _ hz => hsource ⟨hz.1, ⟨by linarith [hz.2.1], hz.2.2⟩⟩
  have hconn : IsPreconnected (H '' S) :=
    (isPreconnected_Icc.prod isPreconnected_Ioo).image H (H.continuousOn.mono hS)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) delta :=
    Ioo_mem_nhdsGT hdelta
  obtain ⟨r, hr, hrU⟩ := (hsmall.and hray).exists
  have hp : H (q, r) ∈ U := by simpa only [hmap, normalStrip] using hrU
  have hsub : H '' S ⊆ U := hconn.subset_of_closure_inter_subset hU
    ⟨H (q, r), ⟨(q, r), ⟨hq, hr⟩, rfl⟩, hp⟩ (by
      rintro z ⟨hz, p, hpS, rfl⟩
      by_contra hn
      have hf : H p ∈ frontier U := ⟨hz, by simpa only [hU.interior_eq] using hn⟩
      rw [hfront] at hf
      exact hpS.2.1.ne' ((hline p (hS hpS)).mp hf))
  exact fun t ht r hr => hsub ⟨(t, r), ⟨ht, hr⟩, rfl⟩

theorem m64Intrinsic_exists_global_inward_orientation
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ g : ℝ → AnnulusCoordinates,
      (g = gamma ∨ g = fun t => gamma (T - t)) ∧
      ContDiff ℝ ∞ g ∧ g 0 = g T ∧ InjOn g (Ico 0 T) ∧
      g '' Icc 0 T = gamma '' Icc 0 T ∧
      (∀ t ∈ Ioo (0 : ℝ) T, deriv g t ≠ 0) ∧
      ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        g t + r • quarterTurn (deriv g t) ∈ U := by
  have hab : T / 3 < 2 * T / 3 := by linarith
  have ha : 0 < T / 3 := by positivity
  have hb : 2 * T / 3 < T := by linarith
  obtain ⟨g, l, u, horient, hg', hend', hinj', hfull, hl, hlu, hu, _, hray⟩ :=
    m64Intrinsic_exists_inward_loop_orientation hg hend hinj hab ha hb
      (fun t ht => hregular t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩)
      hU hV hdisj hfU hfV
  have hreg : ∀ t ∈ Ioo (0 : ℝ) T, deriv g t ≠ 0 := by
    rcases horient with rfl | rfl
    · exact hregular
    · intro t ht
      rw [deriv_comp_const_sub]
      exact neg_ne_zero.mpr (hregular (T - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  let q := (l + u) / 2
  have hq : q ∈ Icc l u := ⟨by dsimp [q]; linarith, by dsimp [q]; linarith⟩
  have hq0 : 0 < q := hl.trans_le hq.1
  have hqT : q < T := hq.2.trans_lt hu
  have hfront : frontier U = g '' Icc 0 T := hfU.trans hfull.symm
  refine ⟨g, horient, hg', hend', hinj', hfull, hreg, ?_⟩
  intro t ht
  have ha' : 0 < min q t := lt_min hq0 ht.1
  have hb' : max q t < T := max_lt hqT ht.2
  obtain ⟨delta, hdelta, H, hsource, hmap, _, _, hline⟩ :=
    m64Intrinsic_exists_loop_normal_neighborhood hg' hend' hinj'
      (min_le_max : min q t ≤ max q t) ha' hb'
      (fun s hs => hreg s ⟨ha'.trans_le hs.1, hs.2.trans_lt hb'⟩)
  have hinside := positive_normal_strip_of_ray hU hfront H hdelta hsource hmap hline
    (show q ∈ Icc (min q t) (max q t) from ⟨min_le_left _ _, le_max_left _ _⟩)
    (hray q hq)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) delta :=
    Ioo_mem_nhdsGT hdelta
  filter_upwards [hsmall] with r hr
  simpa only [hmap, normalStrip] using hinside t ⟨min_le_right _ _, le_max_right _ _⟩ r hr

theorem m64Intrinsic_exists_positive_loop_collar
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a ≤ b) (ha : 0 < a) (hb : b < T)
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0)
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hfront : frontier U = gamma '' Icc 0 T)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma a + r • quarterTurn (deriv gamma a) ∈ U) :
    ∃ delta > 0, ∃ H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates,
      (∀ q, H q = normalStrip gamma q) ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      ∀ t ∈ Icc a b, ∀ r ∈ Icc (0 : ℝ) delta,
        (t, r) ∈ H.source ∧ H (t, r) ∈ closure U ∧ (0 < r → H (t, r) ∈ U) := by
  obtain ⟨rho, hrho, H, hsource, hmap, hH, hHi, hline⟩ :=
    m64Intrinsic_exists_loop_normal_neighborhood hg hend hinj hab ha hb hregular
  have hinside := positive_normal_strip_of_ray hU hfront H hrho hsource hmap hline
    (left_mem_Icc.mpr hab) hray
  refine ⟨rho / 2, half_pos hrho, H, hmap, hH, hHi, ?_⟩
  intro t ht r hr
  have hr' : r < rho := hr.2.trans_lt (half_lt_self hrho)
  have hs : (t, r) ∈ H.source := hsource ⟨ht, ⟨by linarith [hr.1], hr'⟩⟩
  refine ⟨hs, ?_, fun hp => hinside t ht r ⟨hp, hr'⟩⟩
  rcases hr.1.eq_or_lt with hz | hp
  · apply frontier_subset_closure
    rw [hfront]
    exact (hline (t, r) hs).mpr hz.symm
  · exact subset_closure (hinside t ht r ⟨hp, hr'⟩)

end PoincareConjecture
