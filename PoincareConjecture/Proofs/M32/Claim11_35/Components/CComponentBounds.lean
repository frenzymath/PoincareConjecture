import PoincareConjecture.Definitions.Ch11.SingularLimits
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M32

private theorem component_neg_half_nonneg (a : ℝ) : 0 ≤ a ^ (-1 / 2 : ℝ) := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_nonneg _

private theorem component_sqrt_mul_neg_half_le {Q m R : ℝ}
    (hQ : 0 < Q) (hm : 0 < m) (hR : m * Q ≤ R) :
    Real.sqrt Q * R ^ (-1 / 2 : ℝ) ≤ m ^ (-1 / 2 : ℝ) := by
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hm hQ) hR
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  calc
    Real.sqrt Q * R ^ (-1 / 2 : ℝ) ≤ Real.sqrt Q * (m * Q) ^ (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg Q)
    _ = m ^ (-1 / 2 : ℝ) * (Q ^ (1 / 2 : ℝ) * Q ^ (-1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow hm.le hQ.le]
      ring
    _ = m ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add hQ]
      norm_num




theorem c_component_normalized_carrier
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {C B Q m : ℝ}
    (N : SingularCComponent g D C) (hQ : 0 < Q) (hm : 0 < m)
    (hB : C ≤ B) {o : M} (ho : o ∈ N.carrier)
    (hscalar : m ≤ D.scalarCurvature o / Q) :
    N.carrier ⊆ (rescaledMetric g Q hQ).ball o (B * m ^ (-1 / 2 : ℝ)) := by
  have hBpos := N.constant_pos.trans_le hB
  have hmQ : m * Q ≤ D.scalarCurvature o := (le_div_iff₀ hQ).mp hscalar
  have hRpos : 0 < D.scalarCurvature o := (mul_pos hm hQ).trans_le hmQ
  have hbdd : BddBelow (range (fun z : N.carrier => D.scalarCurvature z.val ^ (-1 / 2 : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact component_neg_half_nonneg _
  have hinf : sInf (range (fun z : N.carrier => D.scalarCurvature z.val ^ (-1 / 2 : ℝ))) ≤
      D.scalarCurvature o ^ (-1 / 2 : ℝ) := csInf_le hbdd ⟨⟨o, ho⟩, rfl⟩
  have hdiam : intrinsicDiameter g N.carrier <
      ENNReal.ofReal (B * D.scalarCurvature o ^ (-1 / 2 : ℝ)) := by
    apply N.diameter_upper.trans_le
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left hinf N.constant_pos.le).trans
      (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hRpos.le _))
  intro y hy
  have hintrinsic : intrinsicEDist g N.carrier o y ≤ intrinsicDiameter g N.carrier :=
    le_sSup ⟨(⟨o, ho⟩, ⟨y, hy⟩), rfl⟩
  have hdist : g.edist o y < ENNReal.ofReal (B * D.scalarCurvature o ^ (-1 / 2 : ℝ)) :=
    ((g.edist_le_intrinsicEDist N.carrier o y).trans hintrinsic).trans_lt hdiam
  change (rescaledMetric g Q hQ).edist o y < ENNReal.ofReal _
  rw [rescaledMetric_edist]
  have hmul := ENNReal.mul_lt_mul_right
    (show ENNReal.ofReal (Real.sqrt Q) ≠ 0 from
      (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne') ENNReal.ofReal_ne_top hdist
  apply hmul.trans_le
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left (component_sqrt_mul_neg_half_le hQ hm hmQ) hBpos.le
  nlinarith only [h]

end PoincareConjecture.M32
