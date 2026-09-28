import PoincareConjecture.Proofs.M64.Mathlib.InteriorCurveTraces
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfDiskPolynomialGreen














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff intervalIntegral

namespace PoincareConjecture

open Proofs.M58

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]





def m64BoundaryHalfDiskPlusWeight (theta : ℝ) : ℝ :=
  (1 + Real.cos theta) / 2





def m64BoundaryHalfDiskMinusWeight (theta : ℝ) : ℝ :=
  (1 - Real.cos theta) / 2





def m64BoundaryHalfDiskPlusDerivative (theta : ℝ) : ℝ :=
  -Real.sin theta / 2





def m64BoundaryHalfDiskMinusDerivative (theta : ℝ) : ℝ :=
  Real.sin theta / 2

private theorem m64BoundaryHalfDisk_plus_hasDerivAt (theta : ℝ) :
    HasDerivAt m64BoundaryHalfDiskPlusWeight
      (m64BoundaryHalfDiskPlusDerivative theta) theta := by
  change HasDerivAt (fun t => (1 + Real.cos t) / 2) (-Real.sin theta / 2) theta
  simpa [div_eq_mul_inv, one_div, Pi.add_apply, one_mul, mul_assoc, add_comm, mul_comm] using
    (((hasDerivAt_const theta (1 : ℝ)).add (Real.hasDerivAt_cos theta)).const_mul
      (1 / 2 : ℝ))

private theorem m64BoundaryHalfDisk_minus_hasDerivAt (theta : ℝ) :
    HasDerivAt m64BoundaryHalfDiskMinusWeight
      (m64BoundaryHalfDiskMinusDerivative theta) theta := by
  change HasDerivAt (fun t => (1 - Real.cos t) / 2) (Real.sin theta / 2) theta
  simpa [div_eq_mul_inv, one_div, Pi.sub_apply, one_mul, mul_assoc, sub_eq_add_neg,
    add_comm, mul_comm] using
    (((hasDerivAt_const theta (1 : ℝ)).sub (Real.hasDerivAt_cos theta)).const_mul
      (1 / 2 : ℝ))

private theorem m64BoundaryHalfDisk_plus_continuous :
    Continuous m64BoundaryHalfDiskPlusWeight := by
  change Continuous (fun theta : ℝ => (1 + Real.cos theta) / 2)
  exact (continuous_const.add Real.continuous_cos).div_const (2 : ℝ)

private theorem m64BoundaryHalfDisk_minus_continuous :
    Continuous m64BoundaryHalfDiskMinusWeight := by
  change Continuous (fun theta : ℝ => (1 - Real.cos theta) / 2)
  exact (continuous_const.sub Real.continuous_cos).div_const (2 : ℝ)

private theorem m64BoundaryHalfDisk_plusDerivative_continuous :
    Continuous m64BoundaryHalfDiskPlusDerivative := by
  change Continuous (fun theta : ℝ => -Real.sin theta / 2)
  exact (continuous_neg.comp Real.continuous_sin).div_const (2 : ℝ)

private theorem m64BoundaryHalfDisk_minusDerivative_continuous :
    Continuous m64BoundaryHalfDiskMinusDerivative := by
  change Continuous (fun theta : ℝ => Real.sin theta / 2)
  exact Real.continuous_sin.div_const (2 : ℝ)

private theorem m64BoundaryHalfDisk_exists_primitive
    {U W : ℝ → E}
    (hder : ∀ theta ∈ Ioo (0 : ℝ) Real.pi,
      HasDerivAt U (W theta) theta)
    (hW : IntervalIntegrable W volume 0 Real.pi) :
    ∃ c : E, ∀ theta ∈ Ioo (0 : ℝ) Real.pi,
      U theta = c + ∫ t in (0 : ℝ)..theta, W t := by
  exact interiorCurve_exists_primitive
    (a := (0 : ℝ)) (b := Real.pi) (f := U) (d := W)
    Real.pi_pos hder hW

private theorem m64BoundaryHalfDisk_integrate_by_parts
    {F W : ℝ → E} {weight weightDerivative : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F 0 Real.pi)
    (hW : IntervalIntegrable W volume 0 Real.pi)
    (hweight : Continuous weight)
    (hweightDerivative : ∀ theta : ℝ,
      HasDerivAt weight (weightDerivative theta) theta)
    (hweightI : IntervalIntegrable weightDerivative volume 0 Real.pi)
    (hFder : ∀ theta ∈ Ioo (min (0 : ℝ) Real.pi) (max 0 Real.pi),
      HasDerivAt F (W theta) theta) :
    (∫ theta in (0 : ℝ)..Real.pi,
      weightDerivative theta • F theta + weight theta • W theta) =
      weight Real.pi • F Real.pi - weight 0 • F 0 := by
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi)
    hweight.continuousOn hF.continuousOn
    (fun theta _ => hweightDerivative theta) hFder hweightI hW
  calc
    _ = (∫ theta in (0 : ℝ)..Real.pi,
        weightDerivative theta • F theta) +
        ∫ theta in (0 : ℝ)..Real.pi, weight theta • W theta := by
      rw [intervalIntegral.integral_add
        (hweightI.smul_continuousOn hF.continuousOn)
        (hW.continuousOn_smul hweight.continuousOn)]
    _ = _ := by
      rw [hparts]
      abel

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
private theorem m64BoundaryHalfDisk_eq_uIoc_of_eqOn
    {F U : ℝ → E}
    (hEq : EqOn F U (Ioo (0 : ℝ) Real.pi)) :
    F =ᵐ[volume.restrict (uIoc (0 : ℝ) Real.pi)] U := by
  have hEqIcc : F =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)] U := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with theta htheta
    exact hEq htheta
  rw [uIoc_of_le Real.pi_pos.le]
  exact ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hEqIcc

omit [CompleteSpace E] in
private theorem m64BoundaryHalfDisk_plus_transfer
    {F U W : ℝ → E}
    (hEq : EqOn F U (Ioo (0 : ℝ) Real.pi)) :
    (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskPlusDerivative theta • F theta +
        m64BoundaryHalfDiskPlusWeight theta • W theta) =
      ∫ theta in (0 : ℝ)..Real.pi,
        m64BoundaryHalfDiskPlusWeight theta • W theta +
          m64BoundaryHalfDiskPlusDerivative theta • U theta := by
  have hEqI := m64BoundaryHalfDisk_eq_uIoc_of_eqOn (F := F) (U := U) hEq
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hEqI] with theta htheta
  rw [htheta]
  abel

omit [CompleteSpace E] in
private theorem m64BoundaryHalfDisk_minus_transfer
    {F U W : ℝ → E}
    (hEq : EqOn F U (Ioo (0 : ℝ) Real.pi)) :
    (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskMinusDerivative theta • F theta +
        m64BoundaryHalfDiskMinusWeight theta • W theta) =
      ∫ theta in (0 : ℝ)..Real.pi,
        m64BoundaryHalfDiskMinusWeight theta • W theta +
          m64BoundaryHalfDiskMinusDerivative theta • U theta := by
  have hEqI := m64BoundaryHalfDisk_eq_uIoc_of_eqOn (F := F) (U := U) hEq
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hEqI] with theta htheta
  rw [htheta]
  abel

private theorem m64BoundaryHalfDisk_plus_endpoint
    {F W : ℝ → E}
    (hF : AbsolutelyContinuousOnInterval F 0 Real.pi)
    (hW : IntervalIntegrable W volume 0 Real.pi)
    (hFder : ∀ theta ∈ Ioo (min (0 : ℝ) Real.pi) (max 0 Real.pi),
      HasDerivAt F (W theta) theta) :
    (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskPlusDerivative theta • F theta +
        m64BoundaryHalfDiskPlusWeight theta • W theta) = -F 0 := by
  have hparts := m64BoundaryHalfDisk_integrate_by_parts hF hW
    m64BoundaryHalfDisk_plus_continuous
    m64BoundaryHalfDisk_plus_hasDerivAt
    (m64BoundaryHalfDisk_plusDerivative_continuous.intervalIntegrable 0 Real.pi) hFder
  simpa [m64BoundaryHalfDiskPlusWeight, Real.cos_zero, Real.cos_pi] using hparts

private theorem m64BoundaryHalfDisk_minus_endpoint
    {F W : ℝ → E}
    (hF : AbsolutelyContinuousOnInterval F 0 Real.pi)
    (hW : IntervalIntegrable W volume 0 Real.pi)
    (hFder : ∀ theta ∈ Ioo (min (0 : ℝ) Real.pi) (max 0 Real.pi),
      HasDerivAt F (W theta) theta) :
    (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskMinusDerivative theta • F theta +
        m64BoundaryHalfDiskMinusWeight theta • W theta) = F Real.pi := by
  have hparts := m64BoundaryHalfDisk_integrate_by_parts hF hW
    m64BoundaryHalfDisk_minus_continuous
    m64BoundaryHalfDisk_minus_hasDerivAt
    (m64BoundaryHalfDisk_minusDerivative_continuous.intervalIntegrable 0 Real.pi) hFder
  simpa [m64BoundaryHalfDiskMinusWeight, Real.cos_zero, Real.cos_pi] using hparts

set_option maxHeartbeats 2000000 in

private theorem m64BoundaryHalfDisk_primitive_package
    {U W : ℝ → E}
    (hder : ∀ theta ∈ Ioo (0 : ℝ) Real.pi,
      HasDerivAt U (W theta) theta)
    (hW : IntervalIntegrable W volume 0 Real.pi) :
    ∃ F : ℝ → E,
      AbsolutelyContinuousOnInterval F 0 Real.pi ∧
      EqOn F U (Ioo (0 : ℝ) Real.pi) ∧
      (∀ theta, F theta = F 0 + ∫ t in (0 : ℝ)..theta, W t) ∧
      (∀ theta ∈ Ioo (min (0 : ℝ) Real.pi) (max 0 Real.pi),
        HasDerivAt F (W theta) theta) := by
  obtain ⟨c, hc⟩ := m64BoundaryHalfDisk_exists_primitive hder hW
  let F : ℝ → E := fun theta => c + ∫ t in (0 : ℝ)..theta, W t
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 Real.pi :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  have hF : AbsolutelyContinuousOnInterval F 0 Real.pi :=
    hconst.add
      (PoincareConjecture.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
        (f := W) (a := (0 : ℝ)) (b := Real.pi) (c := 0) hW (by simp))
  have hEq : EqOn F U (Ioo (0 : ℝ) Real.pi) := by
    intro theta htheta
    exact (hc theta htheta).symm
  have hFder : ∀ theta ∈ Ioo (0 : ℝ) Real.pi,
      HasDerivAt F (W theta) theta := by
    intro theta htheta
    have hnear : F =ᶠ[𝓝 theta] U := by
      filter_upwards [Ioo_mem_nhds htheta.1 htheta.2] with y hy
      exact hEq hy
    exact (hder theta htheta).congr_of_eventuallyEq hnear
  have hFder' : ∀ theta ∈ Ioo (min (0 : ℝ) Real.pi) (max 0 Real.pi),
      HasDerivAt F (W theta) theta := by
    intro theta htheta
    apply hFder theta
    simpa [min_eq_left (Real.pi_pos.le), max_eq_right (Real.pi_pos.le)] using htheta
  refine ⟨F, hF, hEq, ?_, hFder'⟩
  intro theta
  simp only [F, intervalIntegral.integral_same, add_zero]




set_option maxHeartbeats 2000000 in






theorem m64BoundaryHalfDisk_cosine_endpoint_transport
    {U W : ℝ → E} {bPlus bMinus : E}
    (hder : ∀ theta ∈ Ioo (0 : ℝ) Real.pi,
      HasDerivAt U (W theta) theta)
    (hW : IntervalIntegrable W volume 0 Real.pi)
    (hplus : (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskPlusWeight theta • W theta +
        m64BoundaryHalfDiskPlusDerivative theta • U theta) = -bPlus)
    (hminus : (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskMinusWeight theta • W theta +
        m64BoundaryHalfDiskMinusDerivative theta • U theta) = bMinus) :
    ∃ F : ℝ → E,
      AbsolutelyContinuousOnInterval F 0 Real.pi ∧
      EqOn F U (Ioo (0 : ℝ) Real.pi) ∧
      (∀ theta, F theta = F 0 + ∫ t in (0 : ℝ)..theta, W t) ∧
      F 0 = bPlus ∧ F Real.pi = bMinus := by
  obtain ⟨F, hF, hEq, hformula, hFder'⟩ :=
    m64BoundaryHalfDisk_primitive_package hder hW
  have hplusTransfer : (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskPlusDerivative theta • F theta +
        m64BoundaryHalfDiskPlusWeight theta • W theta) =
      ∫ theta in (0 : ℝ)..Real.pi,
        m64BoundaryHalfDiskPlusWeight theta • W theta +
          m64BoundaryHalfDiskPlusDerivative theta • U theta :=
    m64BoundaryHalfDisk_plus_transfer (F := F) (U := U) (W := W) hEq
  have hminusTransfer : (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskMinusDerivative theta • F theta +
        m64BoundaryHalfDiskMinusWeight theta • W theta) =
      ∫ theta in (0 : ℝ)..Real.pi,
        m64BoundaryHalfDiskMinusWeight theta • W theta +
          m64BoundaryHalfDiskMinusDerivative theta • U theta :=
    m64BoundaryHalfDisk_minus_transfer (F := F) (U := U) (W := W) hEq
  have hplusF : (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskPlusDerivative theta • F theta +
        m64BoundaryHalfDiskPlusWeight theta • W theta) = -bPlus :=
    hplusTransfer.trans hplus
  have hminusF : (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskMinusDerivative theta • F theta +
        m64BoundaryHalfDiskMinusWeight theta • W theta) = bMinus :=
    hminusTransfer.trans hminus
  have hplusSum : (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskPlusDerivative theta • F theta +
        m64BoundaryHalfDiskPlusWeight theta • W theta) = -F 0 := by
    exact m64BoundaryHalfDisk_plus_endpoint (F := F) (W := W) hF hW hFder'
  have hminusSum : (∫ theta in (0 : ℝ)..Real.pi,
      m64BoundaryHalfDiskMinusDerivative theta • F theta +
        m64BoundaryHalfDiskMinusWeight theta • W theta) = F Real.pi := by
    exact m64BoundaryHalfDisk_minus_endpoint (F := F) (W := W) hF hW hFder'
  refine ⟨F, hF, hEq, hformula, ?_, ?_⟩
  · exact neg_inj.mp (hplusSum.symm.trans hplusF)
  · exact hminusSum.symm.trans hminusF

end PoincareConjecture
