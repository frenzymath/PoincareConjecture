import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalNormalCalculus
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubarcLengthDecrease

noncomputable section
set_option autoImplicit false

open Set

namespace PoincareConjecture

theorem m64Intrinsic_exists_central_boundary_interval
    (N : IntrinsicAnnulus) {a b q : ℝ} (hab : a < b) (hq : 0 < q)
    (hlong : 2 * q < intrinsicBoundaryLength N.metric 1 a b) :
    ∃ l u : ℝ, a < l ∧ l < u ∧ u < b ∧
      intrinsicBoundaryLength N.metric 1 l u = q ∧
      ∀ p ∈ Icc l u, q / 10 ≤ intrinsicBoundaryLength N.metric 1 a p ∧
        q / 10 ≤ intrinsicBoundaryLength N.metric 1 p b := by
  obtain ⟨l, hl, hleft⟩ := m64Intrinsic_exists_boundary_prefix_length N one_ne_zero
    hab (by positivity : 0 < q / 10) (by linarith : q / 10 <
      intrinsicBoundaryLength N.metric 1 a b)
  have hsplit := m64Intrinsic_boundaryLength_subarc_decomposition N one_ne_zero
    (a := a) (b := b) (c := l) (d := l)
  have hzero : intrinsicBoundaryLength N.metric 1 l l = 0 := by
    simp only [intrinsicBoundaryLength, intervalIntegral.integral_same]
  rw [hzero, hleft] at hsplit
  obtain ⟨u, hu, hlength⟩ := m64Intrinsic_exists_boundary_prefix_length N one_ne_zero
    hl.2 hq (by linarith : q < intrinsicBoundaryLength N.metric 1 l b)
  have hsplit' := m64Intrinsic_boundaryLength_subarc_decomposition N one_ne_zero
    (a := a) (b := b) (c := l) (d := u)
  rw [hleft, hlength] at hsplit'
  refine ⟨l, u, hl.1, hu.1, hu.2, hlength, ?_⟩
  intro p hp
  have hleftBound := (m64Intrinsic_boundaryLength_subarc_quantitative N one_ne_zero
    (a := a) (b := p) (c := a) (d := l) le_rfl hl.1.le hp.1).1
  have hrightBound := (m64Intrinsic_boundaryLength_subarc_quantitative N one_ne_zero
    (a := p) (b := b) (c := u) (d := b) hp.2 hu.2.le le_rfl).2
  have haa : intrinsicBoundaryLength N.metric 1 a a = 0 := by
    simp only [intrinsicBoundaryLength, intervalIntegral.integral_same]
  have hbb : intrinsicBoundaryLength N.metric 1 b b = 0 := by
    simp only [intrinsicBoundaryLength, intervalIntegral.integral_same]
  rw [haa, sub_zero, hleft] at hleftBound
  rw [hbb, sub_zero] at hrightBound
  exact ⟨hleftBound, by linarith⟩

end PoincareConjecture
