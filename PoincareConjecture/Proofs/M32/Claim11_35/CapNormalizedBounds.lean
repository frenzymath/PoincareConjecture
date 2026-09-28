import PoincareConjecture.Proofs.M32.Neck.ScalarControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M32

private theorem sqrt_mul_neg_half_le {Q m R : ℝ}
    (hQ : 0 < Q) (hm : 0 < m) (hR : m * Q ≤ R) :
    Real.sqrt Q * R ^ (-1 / 2 : ℝ) ≤ m ^ (-1 / 2 : ℝ) := by
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hm hQ) hR
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  calc
    Real.sqrt Q * R ^ (-1 / 2 : ℝ) ≤
        Real.sqrt Q * (m * Q) ^ (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg Q)
    _ = m ^ (-1 / 2 : ℝ) * (Q ^ (1 / 2 : ℝ) * Q ^ (-1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow hm.le hQ.le]
      ring
    _ = m ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add hQ]
      norm_num




theorem cap_normalized_carrier_and_boundary_scale
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {gM : RiemannianMetric 3 M} (C : CapCertificate gM)
    {Q m : ℝ} (hQ : 0 < Q) (hm : 0 < m)
    {B : ℝ} (hB : C.cap_constant ≤ B) {o : M} (ho : o ∈ C.carrier)
    (hscalar : m ≤ C.connection.scalarCurvature o / Q) :
    C.carrier ⊆ (rescaledMetric gM Q hQ).ball o (B * m ^ (-1 / 2 : ℝ)) ∧
      Q * C.boundary_neck.scale ^ 2 ≤ B / m := by
  have hBpos := C.cap_constant_pos.trans_le hB
  have hRpos := C.scalar_pos o ho
  have hmQ : m * Q ≤ C.connection.scalarCurvature o := (le_div_iff₀ hQ).mp hscalar
  obtain ⟨b, hb, hratio⟩ := C.scalar_ratio
  have hbdd : BddAbove (range (fun y : C.carrier => C.connection.scalarCurvature y.val)) := by
    refine ⟨b * C.connection.scalarCurvature o, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hratio o ho y y.property
  have hsup : C.connection.scalarCurvature o ≤ scalarCurvatureSupOn gM C.connection C.carrier :=
    le_csSup hbdd ⟨⟨o, ho⟩, rfl⟩
  have hdiam : intrinsicDiameter gM C.carrier <
      ENNReal.ofReal (B * C.connection.scalarCurvature o ^ (-1 / 2 : ℝ)) := by
    apply C.intrinsic_diameter_bound.trans_le
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hRpos hsup (by norm_num)) C.cap_constant_pos.le).trans
      (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hRpos.le _))
  constructor
  · intro y hy
    have hintrinsic : intrinsicEDist gM C.carrier o y ≤ intrinsicDiameter gM C.carrier :=
      le_sSup ⟨(⟨o, ho⟩, ⟨y, hy⟩), rfl⟩
    have hdist : gM.edist o y <
        ENNReal.ofReal (B * C.connection.scalarCurvature o ^ (-1 / 2 : ℝ)) :=
      ((gM.edist_le_intrinsicEDist C.carrier o y).trans hintrinsic).trans_lt hdiam
    change (rescaledMetric gM Q hQ).edist o y < ENNReal.ofReal _
    rw [rescaledMetric_edist]
    have hmul := ENNReal.mul_lt_mul_right
      (show ENNReal.ofReal (Real.sqrt Q) ≠ 0 by
        exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne')
      ENNReal.ofReal_ne_top hdist
    apply hmul.trans_le
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (sqrt_mul_neg_half_le hQ hm hmQ) hBpos.le
    nlinarith only [h]
  · let N := C.boundary_neck
    have hcenter : N.center ∈ C.carrier :=
      C.boundary_neck_subset (N.central_sphere_subset N.center_on_central_sphere)
    have hratio' : C.connection.scalarCurvature o ≤ B * C.connection.scalarCurvature N.center :=
      (hratio N.center hcenter o ho).trans
        (mul_le_mul_of_nonneg_right (hb.le.trans hB) (C.scalar_pos _ hcenter).le)
    have hscale := neckScale_sq_mul_scalar_center N
    rw [C.boundary_neck_connection] at hscale
    have h := mul_le_mul_of_nonneg_right (hmQ.trans hratio') (sq_nonneg N.scale)
    apply (le_div_iff₀ hm).mpr
    change Q * N.scale ^ 2 * m ≤ B
    calc
      Q * N.scale ^ 2 * m = m * Q * N.scale ^ 2 := by ring
      _ ≤ B * C.connection.scalarCurvature N.center * N.scale ^ 2 := h
      _ = B * (N.scale ^ 2 * C.connection.scalarCurvature N.center) := by ring
      _ = B := by rw [hscale, mul_one]

end PoincareConjecture.M32
