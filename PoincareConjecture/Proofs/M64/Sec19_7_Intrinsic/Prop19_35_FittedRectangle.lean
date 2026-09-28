import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionRectangle













noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture





theorem m64Intrinsic_region_rectangle_covers_boundary
    {U : Set AnnulusCoordinates}
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {x r sigma : ℝ}
    (hx : (x, 0) ∈ H.source) (hr : 0 < r) (hsigma : sigma = 1 ∨ sigma = -1)
    (hside : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ closure U ↔ 0 ≤ sigma * z.2) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ H (x, 0) ∈ W ∧
      W ∩ closure U ⊆ H '' {q : ℝ × ℝ |
        q.1 ∈ Icc (x - r) (x + r) ∧ sigma * q.2 ∈ Icc (0 : ℝ) r} := by
  have habs : |sigma| = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (H.open_source.mem_nhds hx) hside)
  let d := min R r / 2
  have hd : 0 < d := half_pos (lt_min hR hr)
  have hdR : d < R := (half_lt_self (lt_min hR hr)).trans_le (min_le_left _ _)
  have hdr : d < r := (half_lt_self (lt_min hR hr)).trans_le (min_le_right _ _)
  have hsource : ball (x, (0 : ℝ)) d ⊆ H.source :=
    fun q hq => (hball (mem_ball.mpr ((mem_ball.mp hq).trans hdR))).1
  refine ⟨H '' ball (x, (0 : ℝ)) d,
    H.isOpen_image_of_subset_source isOpen_ball hsource,
      ⟨(x, 0), mem_ball_self hd, rfl⟩, ?_⟩
  rintro z ⟨⟨q, hq, rfl⟩, hz⟩
  have hqR : q ∈ ball (x, (0 : ℝ)) R :=
    mem_ball.mpr ((mem_ball.mp hq).trans hdR)
  have hdist : |q.1 - x| < d ∧ |q.2| < d := by
    simpa only [mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using hq
  have hfirst : q.1 ∈ Icc (x - r) (x + r) := by
    have h := abs_lt.mp (hdist.1.trans hdr)
    constructor <;> linarith [h.1, h.2]
  have hheight : sigma * q.2 ∈ Icc (0 : ℝ) r := by
    refine ⟨(hball hqR).2.mp hz, ?_⟩
    have h := (le_abs_self (sigma * q.2)).trans (by
      simpa only [abs_mul, habs, one_mul] using (hdist.2.trans hdr).le)
    exact h
  exact ⟨q, ⟨hfirst, hheight⟩, rfl⟩





theorem m64Intrinsic_exists_fitted_loop_region_rectangle
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (x r sigma : ℝ)
      (W : Set AnnulusCoordinates),
      0 < r ∧ (sigma = 1 ∨ sigma = -1) ∧ H (x, 0) = gamma p ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      (∀ s ∈ Icc (x - r) (x + r), ∀ t ∈ Icc (0 : ℝ) r,
        (s, sigma * t) ∈ H.source ∧ H (s, sigma * t) ∈ closure U ∧
          (0 < t → H (s, sigma * t) ∈ U)) ∧
      IsOpen W ∧ gamma p ∈ W ∧
      W ∩ closure U ⊆ H '' {q : ℝ × ℝ |
        q.1 ∈ Icc (x - r) (x + r) ∧ sigma * q.2 ∈ Icc (0 : ℝ) r} := by
  obtain ⟨H, x, hx, hbase, hH, hHi, hside⟩ :=
    m64Intrinsic_exists_loop_region_straightening hg hend hinj hp hregular
      hU hV hdisj hfU hfV
  have hsign : ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ closure U ↔ 0 ≤ sigma * z.2 := by
    rcases hside with h | h
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_mul, neg_nonneg] using h⟩
  obtain ⟨sigma, hsigma, hside⟩ := hsign
  obtain ⟨r, hr, hrect⟩ := m64Intrinsic_exists_region_rectangle_of_halfplane
    hU hV hdisj (hfU.trans hfV.symm) H hx hsigma hside
  obtain ⟨W, hW, hpW, hcover⟩ :=
    m64Intrinsic_region_rectangle_covers_boundary H hx hr hsigma hside
  exact ⟨H, x, r, sigma, W, hr, hsigma, hbase, hH, hHi, hrect, hW,
    hbase ▸ hpW, hcover⟩

end PoincareConjecture
