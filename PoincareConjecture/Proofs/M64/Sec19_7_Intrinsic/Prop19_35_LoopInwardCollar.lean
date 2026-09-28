import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopNormalNeighborhood













noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem occupied_strip_of_germ
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    {a b delta sigma : ℝ} (hab : a ≤ b) (hdelta : 0 < delta)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hsource : Icc a b ×ˢ Ioo (-delta) delta ⊆ H.source)
    (hfront : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0)
    (hgerm : ∀ᶠ q in 𝓝 (a, (0 : ℝ)), H q ∈ closure U ↔ 0 ≤ sigma * q.2) :
    ∀ t ∈ Icc a b, ∀ s ∈ Ioo (0 : ℝ) delta, H (t, sigma * s) ∈ U := by
  have hsquare : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  have habs : |sigma| = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  have hsne : sigma ≠ 0 := by intro he; simp [he] at hsquare
  let D := Icc a b ×ˢ Ioo (0 : ℝ) delta
  let F : ℝ × ℝ → AnnulusCoordinates := fun q => H (q.1, sigma * q.2)
  have hDs (q : ℝ × ℝ) (hq : q ∈ D) : (q.1, sigma * q.2) ∈ H.source := by
    apply hsource
    refine ⟨hq.1, abs_lt.mp ?_⟩
    rw [abs_mul, habs, one_mul, abs_of_pos hq.2.1]
    exact hq.2.2
  have hnotfront (q : ℝ × ℝ) (hq : q ∈ D) : F q ∉ frontier U := by
    intro hqf
    have he := (hfront _ (hDs q hq)).mp hqf
    exact (mul_ne_zero hsne hq.2.1.ne') he
  have hclosed (q : ℝ × ℝ) (hq : q ∈ D) (hcl : F q ∈ closure U) : F q ∈ U := by
    by_contra hn
    exact hnotfront q hq ⟨hcl, by simpa only [hU.interior_eq] using hn⟩
  obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp hgerm
  let e := min (delta / 2) (rho / 2)
  have he : 0 < e := lt_min (half_pos hdelta) (half_pos hrho)
  have hed : e < delta := (min_le_left _ _).trans_lt (half_lt_self hdelta)
  have her : e < rho := (min_le_right _ _).trans_lt (half_lt_self hrho)
  have hnear : (a, sigma * e) ∈ ball (a, (0 : ℝ)) rho := by
    rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_mul, habs,
      one_mul, abs_of_pos he, max_eq_right he.le]
    exact her
  have heD : (a, e) ∈ D := ⟨left_mem_Icc.mpr hab, he, hed⟩
  have heU : F (a, e) ∈ U := hclosed _ heD ((hball hnear).mpr (by
    change 0 ≤ sigma * (sigma * e)
    rw [← mul_assoc, hsquare, one_mul]
    exact he.le))
  have hconn : IsPreconnected (F '' D) :=
    (isPreconnected_Icc.prod isPreconnected_Ioo).image F
      (H.continuousOn.comp
        (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn
        hDs)
  have hsub : F '' D ⊆ U := hconn.subset_of_closure_inter_subset hU
    ⟨F (a, e), ⟨(a, e), heD, rfl⟩, heU⟩ (by
      rintro p ⟨hp, q, hq, rfl⟩
      exact hclosed q hq hp)
  exact fun t ht s hs => hsub ⟨(t, s), ⟨ht, hs⟩, rfl⟩




theorem m64Intrinsic_normal_strip_occupied_side
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfrontUV : frontier U = frontier V)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    {a b delta : ℝ} (hab : a ≤ b) (hdelta : 0 < delta)
    (hsource : Icc a b ×ˢ Ioo (-delta) delta ⊆ H.source)
    (hfront : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0) :
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ t ∈ Icc a b, ∀ s ∈ Ioo (0 : ℝ) delta, H (t, sigma * s) ∈ U := by
  have ha : (a, (0 : ℝ)) ∈ H.source :=
    hsource ⟨left_mem_Icc.mpr hab, ⟨by linarith, hdelta⟩⟩
  have hline : ∀ᶠ q in 𝓝 (a, (0 : ℝ)), H q ∈ frontier U ↔ q.2 = 0 := by
    filter_upwards [H.open_source.mem_nhds ha] with q hq using hfront q hq
  rcases m64Intrinsic_jordan_product_line_germ hU hV hdisj hfrontUV H ha
    ((hfront _ ha).mpr rfl) hline with h | h
  · exact ⟨1, Or.inl rfl, occupied_strip_of_germ hU H hab hdelta (Or.inl rfl)
      hsource hfront (by simpa only [one_mul] using h)⟩
  · exact ⟨-1, Or.inr rfl, occupied_strip_of_germ hU H hab hdelta (Or.inr rfl)
      hsource hfront (by simpa only [neg_one_mul, neg_nonneg] using h)⟩





theorem m64Intrinsic_exists_loop_inward_normal_collar
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a ≤ b) (ha : 0 < a) (hb : b < T)
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (delta sigma : ℝ) (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates),
      0 < delta ∧ (sigma = 1 ∨ sigma = -1) ∧
      (∀ q, H q = normalStrip gamma q) ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) delta,
        (t, sigma * s) ∈ H.source ∧ H (t, sigma * s) ∈ closure U ∧
          (0 < s → H (t, sigma * s) ∈ U) := by
  obtain ⟨rho, hrho, H, hsource, hformula, hH, hHi, hline⟩ :=
    m64Intrinsic_exists_loop_normal_neighborhood hg hend hinj hab ha hb hregular
  have hfront : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0 := by
    simpa only [hfU] using hline
  obtain ⟨sigma, hsigma, hinward⟩ := m64Intrinsic_normal_strip_occupied_side
    hU hV hdisj (hfU.trans hfV.symm) H hab hrho hsource hfront
  have habs : |sigma| = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  refine ⟨rho / 2, sigma, H, half_pos hrho, hsigma, hformula, hH, hHi, ?_⟩
  intro t ht s hs
  have hsr : s < rho := hs.2.trans_lt (half_lt_self hrho)
  refine ⟨hsource ⟨ht, abs_lt.mp ?_⟩, ?_, fun hpos => hinward t ht s ⟨hpos, hsr⟩⟩
  · rw [abs_mul, habs, one_mul, abs_of_nonneg hs.1]
    exact hsr
  · rcases hs.1.eq_or_lt with hs0 | hpos
    · have hs0' : s = 0 := hs0.symm
      rw [hs0', mul_zero, hformula, normalStrip_axis]
      apply frontier_subset_closure
      rw [hfU]
      exact ⟨t, ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩, rfl⟩
    · exact subset_closure (hinward t ht s ⟨hpos, hsr⟩)

end PoincareConjecture
