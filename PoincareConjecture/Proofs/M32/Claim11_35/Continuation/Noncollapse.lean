import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.NoncollapseVolume
import PoincareConjecture.Proofs.M32.Claim11_35.Evolving.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds



















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

private theorem backward_center_radius_le_four_scale
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (hscalar : N.scale⁻¹ ^ 2 / 2 <
      F.scalar (N.time_cylinder.pointMap tau htau N.center))
    {r : ℝ} (hr : 0 < r)
    (hcurv : |F.curvatureNorm (N.time_cylinder.pointMap tau htau N.center)| ≤ r⁻¹ ^ 2) :
    r ≤ 4 * N.scale := by
  let p := N.time_cylinder.pointMap tau htau N.center
  have htrace := (F.connection p.1).scalarCurvature_le_curvatureTensorNorm_sharp p.2
  have hR : F.scalar p ≤ 3 * r⁻¹ ^ 2 := by
    exact htrace.trans (by
      norm_num only [Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcurv) (by norm_num))
  have hbound : N.scale⁻¹ ^ 2 / 2 < 3 * r⁻¹ ^ 2 := hscalar.trans_le hR
  have hm := mul_lt_mul_of_pos_left hbound
    (mul_pos (sq_pos_of_pos N.scale_pos) (sq_pos_of_pos hr))
  have hleft : (N.scale ^ 2 * r ^ 2) * (N.scale⁻¹ ^ 2 / 2) = r ^ 2 / 2 := by
    field_simp [N.scale_pos.ne']
  have hright : (N.scale ^ 2 * r ^ 2) * (3 * r⁻¹ ^ 2) = 3 * N.scale ^ 2 := by
    field_simp [hr.ne']
  rw [hleft, hright] at hm
  nlinarith [N.scale_pos]





theorem exists_strongNeck_backward_center_noncollapsed :
    ∃ epsilonNC : ℝ, 0 < epsilonNC ∧ epsilonNC ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
        ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ epsilonNC →
          ∀ {tau : ℝ} (htau : tau ∈ Ioc (-1) 0), -(1 / 2 : ℝ) ≤ tau →
            GeneralizedKappaNoncollapsedAt F
              (N.time_cylinder.pointMap tau htau N.center) neckNoncollapseConstant 1 := by
  obtain ⟨epsilonNC, hpos, hsmall, hscalar⟩ :=
    exists_strongNeck_backward_scalarLaplacian_control.{u}
  refine ⟨epsilonNC, hpos, hsmall, ?_⟩
  intro F t epsilon N hN tau htau hhalf
  have hcenterN : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  have hR := hscalar N hN htau N.center hcenterN
  let p := N.time_cylinder.pointMap tau htau N.center
  have hQ : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hnorm : (3 / 4 : ℝ) < (1 - tau) * F.scalar p / (N.scale⁻¹ ^ 2) := by
    simpa only [normalizedCylinderScalar, dif_pos htau, mul_div_assoc] using hR.2.1
  have hproduct := (lt_div_iff₀ hQ).mp hnorm
  have hhalfScalar : N.scale⁻¹ ^ 2 / 2 < F.scalar p := by
    have hupper : (1 - tau) * F.scalar p ≤ (3 / 2 : ℝ) * F.scalar p :=
      mul_le_mul_of_nonneg_right (by linarith) hR.1.le
    linarith
  intro r hr _hr1 _htime e hidentity hcurv
  have hzero : (0 : ℝ) ∈ Ioc (-r ^ 2) 0 := ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩
  have hcenter : p.2 ∈ (F.metric p.1).ball p.2 r := by
    change (F.metric p.1).edist p.2 p.2 < ENNReal.ofReal r
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hr
  have htest := hcurv 0 hzero p.2 hcenter
  rw [hidentity hzero p.2 hcenter] at htest
  have hrscale := backward_center_radius_le_four_scale N htau hhalfScalar hr htest
  exact strongNeck_backward_center_ball_volume N (hN.trans hsmall) htau hhalf hr hrscale

end PoincareConjecture.M32
