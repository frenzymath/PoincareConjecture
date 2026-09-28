import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CommonCapCoordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture

theorem m64Intrinsic_exists_axis_fitted_corner_caps
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (h0 : (0 : ℝ × ℝ) ∈ H.source)
    (hH : ContDiffOn ℝ ∞ H H.source) (hHi : ContDiffOn ℝ ∞ H.symm H.target) :
    ∃ delta > 0, ∀ r : ℝ, 0 < r → r < delta →
      ∃ (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
        (W : Set AnnulusCoordinates),
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source ∧
        F.target ⊆ H.target ∧
        ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target ∧
        (∀ s ∈ Icc (0 : ℝ) r, F (s, 0) = H (s, 0)) ∧
        (∀ s ∈ Icc (0 : ℝ) r, F (0, s) = H (0, s)) ∧
        (∀ t : ℝ, F ((1 - t) * r, t * r) =
          (1 - t) • F (r, 0) + t • F (0, r)) ∧
        F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
          H '' (H.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
        (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}) ∩
          H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
            H '' ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)) ∧
        IsOpen W ∧ H 0 ∈ W ∧ W ⊆ H.target ∧
        W ∩ H '' (H.source ∩ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ⊆
          F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
  obtain ⟨rho, hrho, hcaps⟩ := exists_smooth_coordinate_corner_caps H h0 hH hHi
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds h0)
  let delta := min rho eta
  refine ⟨delta, lt_min hrho heta, ?_⟩
  intro r hr hrd
  have hrrho : r < rho := hrd.trans_le (min_le_left _ _)
  have hreta : r < eta := hrd.trans_le (min_le_right _ _)
  have hsmall {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) : |s| < rho := by
    rw [abs_of_nonneg hs.1]
    exact hs.2.trans_lt hrrho
  have hfirst_source {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) : (s, (0 : ℝ)) ∈ H.source := by
    apply hball
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, abs_of_nonneg hs.1] using
      And.intro (hs.2.trans_lt hreta) heta
  have hsecond_source {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) : ((0 : ℝ), s) ∈ H.source := by
    apply hball
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, abs_of_nonneg hs.1] using
      And.intro heta (hs.2.trans_lt hreta)
  obtain ⟨F, hsource, htarget, hF, hFi, hfirst, hsecond, hchord, hsign, hsector,
    W, hW, hpW, hWt, hcover⟩ := hcaps r hr hrrho
  refine ⟨F, W, hsource, htarget, hF, hFi, fun s hs => hfirst s (hsmall hs),
    fun s hs => hsecond s (hsmall hs), ?_, hsector, ?_, hW, hpW, hWt, hcover⟩
  · intro t
    rw [hfirst r (hsmall ⟨hr.le, le_rfl⟩), hsecond r (hsmall ⟨hr.le, le_rfl⟩)]
    have h := hchord (1 - t)
    rw [show 1 - (1 - t) = t by ring, add_comm] at h
    exact h
  · ext z
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, p, ⟨hp, hpaxis⟩, hpq⟩
      have hq1 : q.1 ∈ Icc (0 : ℝ) r := ⟨hq.1, by linarith [hq.2.1, hq.2.2]⟩
      have hq2 : q.2 ∈ Icc (0 : ℝ) r := ⟨hq.2.1, by linarith [hq.1, hq.2.2]⟩
      have hinverse : H.symm (F q) = p := by rw [← hpq, H.left_inv hp]
      have hs := hsign q.1 q.2 (hsmall hq1) (hsmall hq2)
      rw [hinverse] at hs
      rcases hpaxis with hp1 | hp2
      · have hzero := hs.1.2.1.mp hp1
        have hqeq : q = (0, q.2) := Prod.ext hzero rfl
        refine ⟨(0, q.2), Or.inr ⟨rfl, hq2⟩, ?_⟩
        rw [hqeq, hsecond _ (hsmall hq2)]
      · have hzero := hs.2.2.1.mp hp2
        have hqeq : q = (q.1, 0) := Prod.ext rfl hzero
        refine ⟨(q.1, 0), Or.inl ⟨hq1, rfl⟩, ?_⟩
        rw [hqeq, hfirst _ (hsmall hq1)]
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
      · have hqeq : q = (q.1, 0) := Prod.ext rfl hq2
        rw [hqeq]
        refine ⟨⟨(q.1, 0), ⟨hq1.1, le_rfl, by simpa using hq1.2⟩,
          hfirst _ (hsmall hq1)⟩, ?_⟩
        exact ⟨(q.1, 0), ⟨hfirst_source hq1, Or.inr rfl⟩, rfl⟩
      · have hqeq : q = (0, q.2) := Prod.ext hq1 rfl
        rw [hqeq]
        refine ⟨⟨(0, q.2), ⟨le_rfl, hq2.1, by simpa using hq2.2⟩,
          hsecond _ (hsmall hq2)⟩, ?_⟩
        exact ⟨(0, q.2), ⟨hsecond_source hq2, Or.inl rfl⟩, rfl⟩

end PoincareConjecture
