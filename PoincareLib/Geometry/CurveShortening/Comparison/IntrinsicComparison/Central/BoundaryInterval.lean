import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Regional.NormalCalculus
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Subarc.LengthDecrease

/-! A local base interval with fixed margins in a long regional base.
Source: MT Lemma 19.46, pp. 477-478; central-regional-descent derivation,
Section 3. The interval is selected by actual metric arclength. -/

noncomputable section
set_option autoImplicit false

open Set

namespace PoincareMT

/-- A base longer than 2q contains an interval of length q whose every point is at least
q/10 from either parent endpoint in actual length. Source: MT Lemma 19.46;
central-regional-descent derivation, Section 3. Source/construction:
proof-work/tasks/M64/derivations/2026-09-27-central-regional-descent.md, Section 3. -/
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

end PoincareMT
