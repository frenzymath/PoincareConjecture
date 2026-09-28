import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryPathLength
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubarcLengthDecrease

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ENNReal Manifold ContDiff

namespace PoincareConjecture

private theorem boundary_side_competitor
    (N : IntrinsicAnnulus) {K : Set AnnulusCoordinates} {p q A : ℝ} (hA : 0 ≤ A)
    {alpha : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hunit : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hstart : alpha 0 = intrinsicAnnulusBoundary 1 q)
    (hside : MapsTo alpha (Icc 0 A) K)
    (hbase : MapsTo (intrinsicAnnulusBoundary 1) (Icc (min p q) (max p q)) K) :
    ∃ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) ∧
      tau 0 = intrinsicAnnulusBoundary 1 p ∧ tau 1 = alpha A ∧ MapsTo tau (Icc 0 1) K ∧
      m64IntrinsicCurveVariation N.metric tau 0 1 ≤
        ENNReal.ofReal (intrinsicBoundaryLength N.metric 1 (min p q) (max p q) + A) := by
  let f := fun t : ℝ => intrinsicAnnulusBoundary 1 (p + (q - p) * t)
  let g := fun t : ℝ => alpha (A * t)
  have hf : ContinuousOn f (Icc 0 1) :=
    ((m64Intrinsic_contDiff_boundary 1).continuous.comp
      (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  have hg : ContinuousOn g (Icc 0 1) :=
    (ha.continuous.comp (continuous_const.mul continuous_id)).continuousOn
  have hj : f 1 = g 0 := by simpa only [f, g, mul_one, add_sub_cancel, mul_zero] using hstart.symm
  have hfp (t : ℝ) (ht : t ∈ Icc 0 1) : p + (q - p) * t ∈ Icc (min p q) (max p q) := by
    rcases le_total p q with hpq | hqp
    · rw [min_eq_left hpq, max_eq_right hpq]
      constructor <;> nlinarith [ht.1, ht.2]
    · rw [min_eq_right hqp, max_eq_left hqp]
      constructor <;> nlinarith [ht.1, ht.2]
  have hgp (t : ℝ) (ht : t ∈ Icc 0 1) : A * t ∈ Icc (0 : ℝ) A := by
    constructor <;> nlinarith [ht.1, ht.2]
  have hfvar : m64IntrinsicCurveVariation N.metric f 0 1 ≤
      ENNReal.ofReal (intrinsicBoundaryLength N.metric 1 (min p q) (max p q)) := by
    rw [show f = (fun t => intrinsicAnnulusBoundary 1 (p + (q - p) * t)) from rfl,
      m64Intrinsic_curveVariation_affine]
    exact m64Intrinsic_boundary_curveVariation_le N one_ne_zero (min_le_max)
  have hgvar : m64IntrinsicCurveVariation N.metric g 0 1 ≤ ENNReal.ofReal A := by
    have hvar := m64Intrinsic_curveVariation_affine N.metric alpha 0 A
    simp only [zero_add, sub_zero, min_eq_left hA, max_eq_right hA] at hvar
    rw [show g = (fun t => alpha (A * t)) from rfl, hvar]
    simpa only [sub_zero] using m64Intrinsic_unit_curveVariation_le N ha hunit
  obtain ⟨tau, htc, ht0, ht1, htimage, htvar⟩ :=
    m64Intrinsic_exists_join_with_variation N.metric hf hg hj
  refine ⟨tau, htc, ?_, ?_, ?_, ?_⟩
  · simpa only [f, mul_zero, add_zero] using ht0
  · simpa only [g, mul_one] using ht1
  · intro t ht
    rcases htimage t ht with ⟨s, hs, heq⟩ | ⟨s, hs, heq⟩
    · exact heq ▸ hbase (hfp s hs)
    · exact heq ▸ hside (hgp s hs)
  · rw [htvar]
    have hlength := m64Intrinsic_boundaryLength_nonneg N 1 (min p q) (max p q) min_le_max
    exact (add_le_add hfvar hgvar).trans_eq (ENNReal.ofReal_add hlength hA).symm

theorem m64Intrinsic_exists_short_collision_competitor
    (N : IntrinsicAnnulus) {K : Set AnnulusCoordinates}
    {a b A B p : ℝ} (hp : p ∈ Icc a b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {alpha beta : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hunitA : ∀ t ∈ Icc 0 A, N.metric.inner (alpha t) (deriv alpha t) (deriv alpha t) = 1)
    (hunitB : ∀ t ∈ Icc 0 B, N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (ha0 : alpha 0 = intrinsicAnnulusBoundary 1 a)
    (hb0 : beta 0 = intrinsicAnnulusBoundary 1 b) (hmeet : alpha A = beta B)
    (hsideA : MapsTo alpha (Icc 0 A) K) (hsideB : MapsTo beta (Icc 0 B) K)
    (hbase : MapsTo (intrinsicAnnulusBoundary 1) (Icc a b) K) :
    ∃ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) ∧
      tau 0 = intrinsicAnnulusBoundary 1 p ∧ tau 1 = alpha A ∧ MapsTo tau (Icc 0 1) K ∧
      m64IntrinsicCurveVariation N.metric tau 0 1 ≤
        ENNReal.ofReal (intrinsicBoundaryLength N.metric 1 a b / 2 + max A B) := by
  have hsum : intrinsicBoundaryLength N.metric 1 a b =
      intrinsicBoundaryLength N.metric 1 a p + intrinsicBoundaryLength N.metric 1 p b := by
    have h := m64Intrinsic_boundaryLength_subarc_decomposition N
      (a := a) (b := b) (c := p) (d := p) one_ne_zero
    simpa only [intrinsicBoundaryLength, intervalIntegral.integral_same, add_zero] using h
  by_cases hleft : intrinsicBoundaryLength N.metric 1 a p ≤ intrinsicBoundaryLength N.metric 1 p b
  · have hbase' : MapsTo (intrinsicAnnulusBoundary 1) (Icc (min p a) (max p a)) K := by
      rw [min_eq_right hp.1, max_eq_left hp.1]
      exact hbase.mono (Icc_subset_Icc le_rfl hp.2) (Subset.rfl)
    obtain ⟨tau, htc, ht0, ht1, htconf, htvar⟩ :=
      boundary_side_competitor N hA ha hunitA ha0 hsideA hbase'
    refine ⟨tau, htc, ht0, ht1, htconf, htvar.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [min_eq_right hp.1, max_eq_left hp.1]
    linarith [le_max_left A B]
  · have hbase' : MapsTo (intrinsicAnnulusBoundary 1) (Icc (min p b) (max p b)) K := by
      rw [min_eq_left hp.2, max_eq_right hp.2]
      exact hbase.mono (Icc_subset_Icc hp.1 le_rfl) (Subset.rfl)
    obtain ⟨tau, htc, ht0, ht1, htconf, htvar⟩ :=
      boundary_side_competitor N hB hb hunitB hb0 hsideB hbase'
    refine ⟨tau, htc, ht0, ht1.trans hmeet.symm, htconf,
      htvar.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [min_eq_left hp.2, max_eq_right hp.2]
    linarith [le_max_right A B]

end PoincareConjecture
