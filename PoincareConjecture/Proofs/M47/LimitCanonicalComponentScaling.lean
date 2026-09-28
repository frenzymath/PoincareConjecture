import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import PoincareConjecture.Proofs.M47.CanonicalComponentSectionalStability
import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingGeometry
import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open M04

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem sectional_lower_of_positive_gram (D : LeviCivitaData g)
    (x : M) (A : ℝ)
    (hA : ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x u v → A < D.sectionalCurvature x u v)
    (u v : TangentSpace (𝓡 3) x) (hgram : 0 < metricGram g x u v) :
    A < D.sectionalCurvature x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨p, q, hp, hq, hpq, hvalue⟩ :=
    M44.exists_orthonormal_curvature_quotient (M13.curvatureTensorLinear D x)
      (fun a b c d => D.curvatureTensor_swap_first x a b c d)
      (fun a b c d => D.curvatureTensor_swap_last x a b c d) u v hgram
  change g.inner x p p = 1 at hp
  change g.inner x q q = 1 at hq
  change g.inner x p q = 0 at hpq
  change D.curvatureTensor x p q p q = D.sectionalCurvature x u v at hvalue
  have h := hA p q ⟨hp, hq, hpq⟩
  simpa only [LeviCivitaData.sectionalCurvature, hp, hq, hpq, one_mul,
    zero_pow (by decide : 2 ≠ 0), sub_zero, div_one, hvalue] using h



noncomputable def limitCanonical_component_unscale (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) {C : ℝ}
    (N : SingularCComponent (M13.scaleSmoothMetric g Q hQ)
      (M13.scaleLeviCivitaData D Q hQ) C) : SingularCComponent g D C := by
  let DQ := M13.scaleLeviCivitaData D Q hQ
  have hsection (x : M) (u v : TangentSpace (𝓡 3) x) :
      DQ.sectionalCurvature x u v = D.sectionalCurvature x u v / Q := by
    simpa only [Diffeomorph.coe_refl, mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
      M13.homothety_sectionalCurvature_eq g (M13.scaleSmoothMetric g Q hQ)
        (Diffeomorph.refl (𝓡 3) M ∞) Q hQ (M13.identity_metricHomothety g Q hQ) D DQ x u v
  have hgram (x : M) (u v : TangentSpace (𝓡 3) x)
      (huv : LeviCivitaData.IsOrthonormalPair g x u v) :
      0 < metricGram (M13.scaleSmoothMetric g Q hQ) x u v := by
    simpa only [metricGram, M13.scaleSmoothMetric_inner, huv.1, huv.2.1, huv.2.2,
      mul_one, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using mul_pos hQ hQ
  have hpos (x : M) (hx : x ∈ N.carrier) : 0 < D.scalarCurvature x := by
    have h := component_scalar_pos N hx
    rw [M13.scaleLeviCivitaData_scalarCurvature] at h
    exact (div_pos_iff_of_pos_right hQ).mp h
  have hradius (x : N.carrier) : DQ.scalarCurvature x.val ^ (-1 / 2 : ℝ) =
      Real.sqrt Q * D.scalarCurvature x.val ^ (-1 / 2 : ℝ) := by
    rw [M13.scaleLeviCivitaData_scalarCurvature,
      Real.div_rpow (hpos x.val x.property).le hQ.le]
    have hpower : Q ^ (-1 / 2 : ℝ) = (Real.sqrt Q)⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hQ.le,
        ← Real.sqrt_eq_rpow]
    rw [hpower, div_inv_eq_mul, mul_comm]
  have hsup : sSup (range (fun x : N.carrier => DQ.scalarCurvature x.val ^ (-1 / 2 : ℝ))) =
      Real.sqrt Q * sSup (range (fun x : N.carrier => D.scalarCurvature x.val ^ (-1 / 2 : ℝ))) := by
    change (⨆ x : N.carrier, DQ.scalarCurvature x.val ^ (-1 / 2 : ℝ)) =
      Real.sqrt Q * ⨆ x : N.carrier, D.scalarCurvature x.val ^ (-1 / 2 : ℝ)
    simp_rw [hradius]
    exact (Real.smul_iSup_of_nonneg (Real.sqrt_nonneg Q)
      (fun x : N.carrier => D.scalarCurvature x.val ^ (-1 / 2 : ℝ))).symm
  have hinf : sInf (range (fun x : N.carrier => DQ.scalarCurvature x.val ^ (-1 / 2 : ℝ))) =
      Real.sqrt Q * sInf (range (fun x : N.carrier => D.scalarCurvature x.val ^ (-1 / 2 : ℝ))) := by
    change (⨅ x : N.carrier, DQ.scalarCurvature x.val ^ (-1 / 2 : ℝ)) =
      Real.sqrt Q * ⨅ x : N.carrier, D.scalarCurvature x.val ^ (-1 / 2 : ℝ)
    simp_rw [hradius]
    exact (Real.smul_iInf_of_nonneg (Real.sqrt_nonneg Q)
      (fun x : N.carrier => D.scalarCurvature x.val ^ (-1 / 2 : ℝ))).symm
  have hc0 : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne'
  refine {
    constant_pos := N.constant_pos
    basepoint := N.basepoint
    carrier := N.carrier
    component_eq := N.component_eq
    compact := N.compact
    topology := N.topology
    positive_sectional := ?_
    sectional_lower := ?_
    diameter_lower := ?_
    diameter_upper := ?_
  }
  · intro x hx u v huv
    have h := sectional_lower_of_positive_gram DQ x 0 (N.positive_sectional x hx)
      u v (hgram x u v huv)
    rw [hsection] at h
    exact (div_pos_iff_of_pos_right hQ).mp h
  · intro x hx u v huv
    have h := sectional_lower_of_positive_gram DQ x
      (C⁻¹ * scalarCurvatureSupOn (M13.scaleSmoothMetric g Q hQ) DQ N.carrier)
      (N.sectional_lower x hx) u v (hgram x u v huv)
    rw [hsection, M13.scaleSmoothMetric_scalarCurvatureSupOn, ← mul_div_assoc] at h
    exact (div_lt_div_iff_of_pos_right hQ).mp h
  · have h := N.diameter_lower
    rw [hsup, M13.scaleSmoothMetric_intrinsicDiameter, mul_left_comm C⁻¹,
      ENNReal.ofReal_mul (Real.sqrt_nonneg Q)] at h
    exact (ENNReal.mul_lt_mul_iff_right hc0 ENNReal.ofReal_ne_top).mp h
  · have h := N.diameter_upper
    rw [hinf, M13.scaleSmoothMetric_intrinsicDiameter, mul_left_comm C,
      ENNReal.ofReal_mul (Real.sqrt_nonneg Q)] at h
    exact (ENNReal.mul_lt_mul_iff_right hc0 ENNReal.ofReal_ne_top).mp h

end PoincareConjecture.M47
