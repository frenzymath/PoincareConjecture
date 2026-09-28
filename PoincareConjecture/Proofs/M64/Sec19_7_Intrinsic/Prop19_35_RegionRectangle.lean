import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopRegionChart

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_exists_region_rectangle_of_halfplane
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfront : frontier U = frontier V)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {x sigma : ℝ}
    (hx : (x, 0) ∈ H.source) (hsigma : sigma = 1 ∨ sigma = -1)
    (hside : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ closure U ↔ 0 ≤ sigma * z.2) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc (x - r) (x + r), ∀ t ∈ Icc (0 : ℝ) r,
      (s, sigma * t) ∈ H.source ∧ H (s, sigma * t) ∈ closure U ∧
        (0 < t → H (s, sigma * t) ∈ U) := by
  have hsquare : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  have habs : |sigma| = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (H.open_source.mem_nhds hx) hside)
  let A : Set (ℝ × ℝ) := ball (x, (0 : ℝ)) R ∩ {z | 0 < sigma * z.2}
  have hA : IsOpen A := isOpen_ball.inter
    (isOpen_lt continuous_const (continuous_const.mul continuous_snd))
  have hAsource : A ⊆ H.source := fun _ hz => (hball hz.1).1
  have himage : H '' A ⊆ closure U := by
    rintro y ⟨z, hz, rfl⟩
    exact (hball hz.1).2.mpr hz.2.le
  have hUregular := (m64Intrinsic_jordan_interior_closure hU hV hdisj hfront).1
  have hinside : H '' A ⊆ U := by
    rw [← hUregular]
    exact (H.isOpen_image_of_subset_source hA hAsource).subset_interior_iff.mpr himage
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro s hs t ht
  have hnear : (s, sigma * t) ∈ ball (x, (0 : ℝ)) R := by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero,
      abs_mul, habs, one_mul, abs_of_nonneg ht.1]
    apply max_lt
    · exact (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩).trans_lt (half_lt_self hR)
    · exact ht.2.trans_lt (half_lt_self hR)
  have hsign : sigma * (sigma * t) = t := by rw [← mul_assoc, hsquare, one_mul]
  refine ⟨(hball hnear).1, (hball hnear).2.mpr (by simpa only [hsign] using ht.1), ?_⟩
  intro htpos
  apply hinside
  refine ⟨(s, sigma * t), ⟨hnear, ?_⟩, rfl⟩
  change 0 < sigma * (sigma * t)
  rw [hsign]
  exact htpos

theorem m64Intrinsic_exists_loop_region_rectangle
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (x r sigma : ℝ),
      0 < r ∧ (sigma = 1 ∨ sigma = -1) ∧ H (x, 0) = gamma p ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      ∀ s ∈ Icc (x - r) (x + r), ∀ t ∈ Icc (0 : ℝ) r,
        (s, sigma * t) ∈ H.source ∧ H (s, sigma * t) ∈ closure U ∧
          (0 < t → H (s, sigma * t) ∈ U) := by
  obtain ⟨H, x, hx, hbase, hH, hHi, hside⟩ :=
    m64Intrinsic_exists_loop_region_straightening hg hend hinj hp hregular
      hU hV hdisj hfU hfV
  rcases hside with hside | hside
  · obtain ⟨r, hr, hrect⟩ := m64Intrinsic_exists_region_rectangle_of_halfplane
      hU hV hdisj (hfU.trans hfV.symm) H hx (sigma := 1) (Or.inl rfl) (by
        simpa only [one_mul] using hside)
    exact ⟨H, x, r, 1, hr, Or.inl rfl, hbase, hH, hHi, hrect⟩
  · obtain ⟨r, hr, hrect⟩ := m64Intrinsic_exists_region_rectangle_of_halfplane
      hU hV hdisj (hfU.trans hfV.symm) H hx (sigma := -1) (Or.inr rfl) (by
        simpa only [neg_one_mul, neg_nonneg] using hside)
    exact ⟨H, x, r, -1, hr, Or.inr rfl, hbase, hH, hHi, hrect⟩

end PoincareConjecture
