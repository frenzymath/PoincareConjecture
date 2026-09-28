import PoincareConjecture.Proofs.M64.Mathlib.FirstLastFrontier
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionMinimizer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ENNReal

namespace PoincareConjecture

private theorem affine_variation_le
    (G : RiemannianMetric 2 AnnulusCoordinates) {f : ℝ → AnnulusCoordinates}
    {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      G.edist (f s) (f t) ≤ ENNReal.ofReal (C * |s - t|))
    {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hab : a ≤ b) :
    m64IntrinsicCurveVariation G (fun t => f (a + (b - a) * t)) 0 1 ≤
      ENNReal.ofReal ((b - a) * C) := by
  have hparam : MapsTo (fun t : ℝ => a + (b - a) * t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> nlinarith [ha.1, hb.2, ht.1, ht.2]
  apply m64Intrinsic_curveVariation_le_of_edist_le G
    (mul_nonneg (sub_nonneg.mpr hab) hC)
  intro s hs t ht
  convert hlip _ (hparam hs) _ (hparam ht) using 1
  congr 1
  rw [show a + (b - a) * s - (a + (b - a) * t) = (b - a) * (s - t) by ring,
    abs_mul, abs_of_nonneg (sub_nonneg.mpr hab)]
  ring

theorem m64Intrinsic_exists_confined_competitor_of_frontier_segments
    (G : RiemannianMetric 2 AnnulusCoordinates) {K O : Set AnnulusCoordinates}
    (hK : IsClosed K) {f : ℝ → AnnulusCoordinates}
    (hc : ContinuousOn f (Icc 0 1)) (h0 : f 0 ∈ K) (h1 : f 1 ∈ K)
    (hO : MapsTo f (Icc 0 1) O) {C : ℝ} (hC : 0 ≤ C)
    (hlip : ∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      G.edist (f s) (f t) ≤ ENNReal.ofReal (C * |s - t|))
    (hside : ∀ p ∈ frontier K ∩ O, ∀ q ∈ frontier K ∩ O,
      ∃ g : ℝ → AnnulusCoordinates, ContinuousOn g (Icc 0 1) ∧
        g 0 = p ∧ g 1 = q ∧ MapsTo g (Icc 0 1) K ∧
        m64IntrinsicCurveVariation G g 0 1 ≤ G.edist p q) :
    ∃ g : ℝ → AnnulusCoordinates, ContinuousOn g (Icc 0 1) ∧
      g 0 = f 0 ∧ g 1 = f 1 ∧ MapsTo g (Icc 0 1) K ∧
      m64IntrinsicCurveVariation G g 0 1 ≤ ENNReal.ofReal C := by
  rcases m64_path_confined_or_first_last_frontier hK hc h0 h1 with hconf | hcontacts
  · exact ⟨f, hc, rfl, rfl, hconf, m64Intrinsic_curveVariation_le_of_edist_le G hC hlip⟩
  obtain ⟨a, b, ha, hb, hab, hfa, hfb, hleft, hright⟩ := hcontacts
  obtain ⟨g, hgc, hg0, hg1, hgconf, hgvar⟩ :=
    hside (f a) ⟨hfa, hO ha⟩ (f b) ⟨hfb, hO hb⟩
  let l := fun t : ℝ => f (0 + (a - 0) * t)
  let r := fun t : ℝ => f (b + (1 - b) * t)
  have hlmap : MapsTo (fun t : ℝ => 0 + (a - 0) * t) (Icc 0 1) (Icc 0 a) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha.1]
  have hrmap : MapsTo (fun t : ℝ => b + (1 - b) * t) (Icc 0 1) (Icc b 1) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, hb.2]
  have hlc : ContinuousOn l (Icc 0 1) :=
    (hc.mono (Icc_subset_Icc le_rfl ha.2)).comp (by fun_prop) hlmap
  have hrc : ContinuousOn r (Icc 0 1) :=
    (hc.mono (Icc_subset_Icc hb.1 le_rfl)).comp (by fun_prop) hrmap
  have hl1 : l 1 = g 0 := by simp only [l, sub_zero, zero_add, mul_one, hg0]
  obtain ⟨q, hqc, hq0, hq1, hqimage, hqvar⟩ :=
    m64Intrinsic_exists_join_with_variation G hlc hgc hl1
  have hqr : q 1 = r 0 := by simp only [hq1, hg1, r, mul_zero, add_zero]
  obtain ⟨tau, htc, ht0, ht1, htimage, htvar⟩ :=
    m64Intrinsic_exists_join_with_variation G hqc hrc hqr
  refine ⟨tau, htc, ?_, ?_, ?_, ?_⟩
  · simpa only [hq0, l, mul_zero, add_zero] using ht0
  · simpa only [r, mul_one, add_sub_cancel] using ht1
  · intro t ht
    rcases htimage t ht with ⟨s, hs, heq⟩ | ⟨s, hs, heq⟩
    · rw [← heq]
      rcases hqimage s hs with ⟨u, hu, heq'⟩ | ⟨u, hu, heq'⟩
      · rw [← heq']
        exact hleft (hlmap hu)
      · rw [← heq']
        exact hgconf hu
    · rw [← heq]
      exact hright (hrmap hs)
  · have hlvar := affine_variation_le G hC hlip (by simp : (0 : ℝ) ∈ Icc 0 1) ha ha.1
    have hrvar := affine_variation_le G hC hlip hb (by simp : (1 : ℝ) ∈ Icc 0 1) hb.2
    have hgvar' : m64IntrinsicCurveVariation G g 0 1 ≤ ENNReal.ofReal ((b - a) * C) := by
      have h := hgvar.trans (hlip a ha b hb)
      simpa only [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub, mul_comm] using h
    rw [htvar, hqvar]
    apply (add_le_add (add_le_add hlvar hgvar') hrvar).trans_eq
    rw [← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr ha.1) hC)
      (mul_nonneg (sub_nonneg.mpr hab) hC),
      ← ENNReal.ofReal_add
        (add_nonneg (mul_nonneg (sub_nonneg.mpr ha.1) hC)
          (mul_nonneg (sub_nonneg.mpr hab) hC))
        (mul_nonneg (sub_nonneg.mpr hb.2) hC)]
    congr 1
    ring

end PoincareConjecture
