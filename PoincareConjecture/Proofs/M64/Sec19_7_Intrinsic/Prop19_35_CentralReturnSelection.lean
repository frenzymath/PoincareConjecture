import PoincareConjecture.Proofs.M64.Mathlib.WeightedCentralInterval
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CentralSubarc
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurveEndpointProjection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_central_circle_return
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e) {height : ℝ → ℝ} (hh : Measurable height)
    {a b epsilon : ℝ} (hab : a < b) (hepsilon : 0 < epsilon)
    (harc : 2 * epsilon < intrinsicBoundaryLength N.metric 1 a b)
    {Z : Set ℝ} (hZ : MeasurableSet Z) (hZsub : Z ⊆ Icc a b)
    (hinj : InjOn (fun z => e !₂[z, height z]) Z)
    (hregular : ∀ z ∈ Z, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[z, height z]))
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target)
    {rho : ℝ} (hrho : 0 ≤ rho) (htargetInj : InjOn target (Icc 0 rho))
    (hunit : ∀ t ∈ Icc 0 rho,
      N.metric.inner (target t) (deriv target t) (deriv target t) = 1)
    (hend : ∀ z ∈ Z, e !₂[z, height z] ∈
      intrinsicAnnulusBoundary 1 '' Icc a b ∪ target '' Icc 0 rho)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ z ∈ Z, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 z ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[z, height z])
          (fderiv ℝ e !₂[z, height z] v) (fderiv ℝ e !₂[z, height z] v))
    (hbudget : rho < c * ((∫ z in Z, intrinsicBoundarySpeed N.metric 1 z) - 2 * epsilon)) :
    ∃ z ∈ Z, ∃ w ∈ Icc a b,
      z ∈ Ioo a b ∧ e !₂[z, height z] = intrinsicAnnulusBoundary 1 w ∧
      e !₂[z, height z] ∉ target '' Icc 0 rho ∧
      epsilon ≤ intrinsicBoundaryLength N.metric 1 a z ∧
      epsilon ≤ intrinsicBoundaryLength N.metric 1 z b := by
  obtain ⟨p, q, hap, hpq, hqb, hleft, hright, hcentral⟩ :=
    m64Intrinsic_exists_central_boundary_subarc N (by norm_num : (1 : ℝ) ≠ 0)
      hab hepsilon harc
  let S := Z ∩ Icc p q
  have hS : MeasurableSet S := hZ.inter measurableSet_Icc
  have hSZ : S ⊆ Z := inter_subset_left
  have hSsub : S ⊆ Icc a b := hSZ.trans hZsub
  have hspeed := (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hmass := m64_setIntegral_inter_Icc_lower_bound (mu := volume) hap.le hpq.le hqb.le
    hspeed.integrableOn_Icc (fun x _ => Real.sqrt_nonneg _) hZsub
  change (∫ z in Z, intrinsicBoundarySpeed N.metric 1 z) -
      intrinsicBoundaryLength N.metric 1 a p - intrinsicBoundaryLength N.metric 1 q b ≤
    ∫ z in S, intrinsicBoundarySpeed N.metric 1 z at hmass
  rw [hleft, hright] at hmass
  have hex : ∃ z ∈ S, e !₂[z, height z] ∉ target '' Icc 0 rho := by
    by_contra hn
    have htargetAll : ∀ z ∈ S, e !₂[z, height z] ∈ target '' Icc 0 rho := by
      simpa only [not_exists, not_and, not_not] using hn
    have hlength := m64Intrinsic_unit_curve_endpoint_projection_length_le
      N e he hh hS hSsub (hinj.mono hSZ) (fun z hz => hregular z (hSZ hz))
      htarget hrho htargetInj hunit htargetAll hc (fun z hz => hbound z (hSZ hz))
    have hscaled := mul_le_mul_of_nonneg_left hmass hc
    have hlength' : c * (∫ z in S, intrinsicBoundarySpeed N.metric 1 z) ≤ rho := by
      simpa only [sub_zero] using hlength
    linarith
  obtain ⟨z, hz, hznot⟩ := hex
  have hcircle := (hend z hz.1).resolve_right hznot
  obtain ⟨w, hw, heq⟩ := hcircle
  exact ⟨z, hz.1, w, hw, ⟨hap.trans_le hz.2.1, hz.2.2.trans_lt hqb⟩,
    heq.symm, hznot, hcentral z hz.2⟩

end PoincareConjecture
