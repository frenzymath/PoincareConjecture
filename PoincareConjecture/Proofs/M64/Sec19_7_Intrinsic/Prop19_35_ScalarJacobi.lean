import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SurfaceCurvature
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryArithmetic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture




theorem m64Intrinsic_spherical_wronskian_nonneg
    {R : ℝ} (hR : 0 < R) (hRpi : R ≤ Real.pi)
    {J J' J'' : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hineq : ∀ t ∈ Ioo (0 : ℝ) R, 0 ≤ J'' t + J t) :
    ∀ t ∈ Icc (0 : ℝ) R,
      0 ≤ J' t * Real.sin t - J t * Real.cos t := by
  have hJc : ContinuousOn J (Icc (0 : ℝ) R) :=
    fun t ht => (hJ t ht).continuousAt.continuousWithinAt
  have hWc : ContinuousOn (fun t => J' t * Real.sin t - J t * Real.cos t)
      (Icc (0 : ℝ) R) :=
    (hJ'.mul Real.continuous_sin.continuousOn).sub
      (hJc.mul Real.continuous_cos.continuousOn)
  have hWd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      HasDerivAt (J' * Real.sin - J * Real.cos)
        ((J'' t + J t) * Real.sin t) t := by
    convert! ((hJ'' t ht).mul (Real.hasDerivAt_sin t)).sub
      ((hJ t ⟨ht.1.le, ht.2.le⟩).mul (Real.hasDerivAt_cos t)) using 1
    ring
  have hmono : MonotoneOn (fun t => J' t * Real.sin t - J t * Real.cos t)
      (Icc (0 : ℝ) R) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hWc
      (fun t ht => (hWd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using ht
    exact mul_nonneg (hineq t ht')
      (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1.le (ht'.2.le.trans hRpi))
  intro t ht
  simpa only [Real.sin_zero, Real.cos_zero, hzero, mul_zero, mul_one, sub_zero]
    using hmono ⟨le_rfl, hR.le⟩ ht ht.1




theorem m64Intrinsic_spherical_wronskian_nonneg_of_jacobi
    {R : ℝ} (hR : 0 < R) (hRpi : R ≤ Real.pi)
    {J J' J'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 ≤ J t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ 1) :
    ∀ t ∈ Icc (0 : ℝ) R,
      0 ≤ J' t * Real.sin t - J t * Real.cos t := by
  apply m64Intrinsic_spherical_wronskian_nonneg hR hRpi hJ hJ' hJ'' hzero
  intro t ht
  have hprod := mul_nonneg (sub_nonneg.mpr (hk t ht)) (hpos t ht)
  nlinarith [hjac t ht]





theorem m64Intrinsic_scaled_spherical_wronskian_nonneg_of_jacobi
    {R κ : ℝ} (hR : 0 < R) (hκ : 0 ≤ κ) (hRpi : κ * R ≤ Real.pi)
    {J J' J'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 ≤ J t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ κ ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) R,
      0 ≤ J' t * Real.sin (κ * t) - κ * J t * Real.cos (κ * t) := by
  have hJc : ContinuousOn J (Icc (0 : ℝ) R) :=
    fun t ht => (hJ t ht).continuousAt.continuousWithinAt
  have hlin : Continuous (fun t : ℝ => κ * t) :=
    continuous_const.mul continuous_id
  have hsin_c : ContinuousOn (fun t : ℝ => Real.sin (κ * t))
      (Icc (0 : ℝ) R) :=
    (Real.continuous_sin.comp hlin).continuousOn
  have hcos_c : ContinuousOn (fun t : ℝ => Real.cos (κ * t))
      (Icc (0 : ℝ) R) :=
    (Real.continuous_cos.comp hlin).continuousOn
  have hWc : ContinuousOn
      (fun t => J' t * Real.sin (κ * t) - κ * J t * Real.cos (κ * t))
      (Icc (0 : ℝ) R) := by
    exact (hJ'.mul hsin_c).sub ((continuousOn_const.mul hJc).mul hcos_c)
  have hWd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      HasDerivAt (fun s => J' s * Real.sin (κ * s) -
          κ * J s * Real.cos (κ * s))
        ((J'' t + κ ^ 2 * J t) * Real.sin (κ * t)) t := by
    have hlin' : HasDerivAt (fun s : ℝ => κ * s) κ t := by
      simpa [id_eq] using (hasDerivAt_id t).const_mul κ
    have hsin' : HasDerivAt (fun s : ℝ => Real.sin (κ * s))
        (κ * Real.cos (κ * t)) t := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_sin (κ * t)).comp t hlin'
    have hcos' : HasDerivAt (fun s : ℝ => Real.cos (κ * s))
        (-κ * Real.sin (κ * t)) t := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_cos (κ * t)).comp t hlin'
    convert! ((hJ'' t ht).mul hsin').sub
      ((hJ t ⟨ht.1.le, ht.2.le⟩).mul hcos' |>.const_mul κ) using 1
    · funext s
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring
    · ring_nf
  have hmono : MonotoneOn
      (fun t => J' t * Real.sin (κ * t) - κ * J t * Real.cos (κ * t))
      (Icc (0 : ℝ) R) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hWc
      (fun t ht => (hWd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using ht
    have hsin : 0 ≤ Real.sin (κ * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        (mul_nonneg hκ ht'.1.le)
        ((mul_le_mul_of_nonneg_left ht'.2.le hκ).trans hRpi)
    have hcoef : 0 ≤ J'' t + κ ^ 2 * J t := by
      have hprod := mul_nonneg (sub_nonneg.mpr (hk t ht')) (hpos t ht')
      nlinarith [hjac t ht']
    exact mul_nonneg hcoef hsin
  intro t ht
  simpa only [Real.sin_zero, Real.cos_zero, hzero, mul_zero, mul_one, sub_zero]
    using hmono ⟨le_rfl, hR.le⟩ ht ht.1



theorem m64Intrinsic_scaled_jacobi_log_derivative_ge_cot
    {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ) (hRpi : κ * R ≤ Real.pi)
    {J J' J'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 < J t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ κ ^ 2)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) R) :
    κ * Real.cos (κ * t) / Real.sin (κ * t) ≤ J' t / J t := by
  have hW := m64Intrinsic_scaled_spherical_wronskian_nonneg_of_jacobi
    hR hκ.le hRpi hJ hJ' hJ'' hzero (fun s hs => (hpos s hs).le) hjac hk t
      ⟨ht.1.le, ht.2.le⟩
  have hsin : 0 < Real.sin (κ * t) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos hκ ht.1
    · exact (mul_lt_mul_of_pos_left ht.2 hκ).trans_le hRpi
  apply (div_le_div_iff₀ hsin (hpos t ht)).mpr
  nlinarith





theorem m64Intrinsic_scaled_jacobi_log_derivative_ge_cot_of_gaussian
    (N : IntrinsicAnnulus) (K κ : ℝ)
    (hK : N.GaussianCurvatureBound K)
    (hκ : 0 < κ) (hKκ : K ≤ κ ^ 2)
    {R : ℝ} (hR : 0 < R) (hRpi : κ * R ≤ Real.pi)
    {q : ℝ → AnnulusCoordinates} {J J' J'' : ℝ → ℝ}
    (hmap : ∀ t ∈ Ioo (0 : ℝ) R, q t ∈ standardAnnulusDomain)
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 < J t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R,
      J'' t + (N.connection.scalarCurvature (q t) / 2) * J t = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) R) :
    κ * Real.cos (κ * t) / Real.sin (κ * t) ≤ J' t / J t := by
  exact m64Intrinsic_scaled_jacobi_log_derivative_ge_cot hR hκ hRpi hJ hJ'
    hJ'' hzero hpos hjac
    (fun s hs => (hK (q s) (hmap s hs)).trans hKκ) ht




theorem m64Intrinsic_jacobi_log_derivative_ge_sqrt_max_cot_of_gaussian
    (N : IntrinsicAnnulus) (K : ℝ)
    (hK : N.GaussianCurvatureBound K)
    {R : ℝ} (hR : 0 < R)
    (hRpi : Real.sqrt (max K 1) * R ≤ Real.pi)
    {q : ℝ → AnnulusCoordinates} {J J' J'' : ℝ → ℝ}
    (hmap : ∀ t ∈ Ioo (0 : ℝ) R, q t ∈ standardAnnulusDomain)
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 < J t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R,
      J'' t + (N.connection.scalarCurvature (q t) / 2) * J t = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) R) :
    Real.sqrt (max K 1) * Real.cos (Real.sqrt (max K 1) * t) /
        Real.sin (Real.sqrt (max K 1) * t) ≤ J' t / J t := by
  have hmax : 0 ≤ max K 1 := by
    exact le_trans (by norm_num) (le_max_right K 1)
  have hκ : 0 < Real.sqrt (max K 1) := by
    exact Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one (le_max_right K 1))
  have hsq : (Real.sqrt (max K 1)) ^ 2 = max K 1 :=
    Real.sq_sqrt hmax
  have hKκ : K ≤ (Real.sqrt (max K 1)) ^ 2 := by
    nlinarith [le_max_left K 1, hsq]
  exact m64Intrinsic_scaled_jacobi_log_derivative_ge_cot_of_gaussian N K
    (Real.sqrt (max K 1)) hK hκ hKκ hR hRpi hmap hJ hJ' hJ'' hzero hpos
    hjac ht




theorem m64Intrinsic_jacobi_log_derivative_ge_cot
    {R : ℝ} (hR : 0 < R) (hRpi : R ≤ Real.pi)
    {J J' J'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 < J t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) R) :
    Real.cos t / Real.sin t ≤ J' t / J t := by
  have hW := m64Intrinsic_spherical_wronskian_nonneg_of_jacobi hR hRpi
    hJ hJ' hJ'' hzero (fun s hs => (hpos s hs).le) hjac hk t
      ⟨ht.1.le, ht.2.le⟩
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans_le hRpi)
  apply (div_le_div_iff₀ hsin (hpos t ht)).mpr
  nlinarith




theorem m64Intrinsic_focusing_base_length_le_turning
    {R L T : ℝ} (hR : 0 < R) (hRquarter : R ≤ Real.pi / 4)
    (_hL : 0 ≤ L) (hT : 0 ≤ T)
    (hendpoint : Real.cos R * L ≤ Real.sin R * T) :
    L ≤ T := by
  have hRpi : R ≤ Real.pi := by
    calc
      R ≤ Real.pi / 4 := hRquarter
      _ ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos : 0 < Real.cos R := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos, hRquarter]
  have hsin_cos : Real.sin R ≤ Real.cos R := by
    rw [← Real.cos_pi_div_two_sub]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact hR.le
    · nlinarith [Real.pi_pos, hR]
    · nlinarith [Real.pi_pos, hRquarter]
  have hturn : Real.sin R * T ≤ Real.cos R * T :=
    mul_le_mul_of_nonneg_right hsin_cos hT
  have hprod : Real.cos R * L ≤ Real.cos R * T :=
    hendpoint.trans hturn
  exact (le_of_mul_le_mul_left hprod hcos)




theorem m64Intrinsic_focusing_base_length_lt_of_small_turning
    (N : IntrinsicAnnulus) {delta r R L a b : ℝ}
    (hturning : N.SmallBoundaryTurning delta r)
    (hab : a ≤ b) (hperiod : b ≤ a + rampPeriod)
    (hsub : intrinsicBoundaryLength N.metric 1 a b ≤ r)
    (hR : 0 < R) (hRquarter : R ≤ Real.pi / 4)
    (hL : 0 ≤ L)
    (hendpoint : Real.cos R * L ≤ Real.sin R *
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) :
    L < delta := by
  have hturn : 0 ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b :=
    m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 a b hab
  have hbase := m64Intrinsic_focusing_base_length_le_turning
    hR hRquarter hL hturn hendpoint
  have hsmall : ∀ a b : ℝ, a ≤ b → b ≤ a + rampPeriod →
      intrinsicBoundaryLength N.metric 1 a b ≤ r →
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b <
          delta := by
    simpa only [IntrinsicAnnulus.SmallBoundaryTurning] using hturning
  exact lt_of_le_of_lt hbase
    (hsmall a b hab hperiod hsub)



theorem m64Intrinsic_scaled_focusing_base_length_le_turning
    {R κ L T : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hangle : κ * R ≤ Real.pi / 4)
    (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hendpoint : Real.cos (κ * R) * L ≤ Real.sin (κ * R) * T) :
    L ≤ T := by
  exact m64Intrinsic_focusing_base_length_le_turning
    (mul_pos hκ hR) hangle hL hT hendpoint



theorem m64Intrinsic_scaled_focusing_base_length_lt_of_small_turning
    (N : IntrinsicAnnulus) {delta r R κ L a b : ℝ}
    (hturning : N.SmallBoundaryTurning delta r)
    (hab : a ≤ b) (hperiod : b ≤ a + rampPeriod)
    (hsub : intrinsicBoundaryLength N.metric 1 a b ≤ r)
    (hR : 0 < R) (hκ : 0 < κ)
    (hangle : κ * R ≤ Real.pi / 4)
    (hL : 0 ≤ L)
    (hendpoint : Real.cos (κ * R) * L ≤ Real.sin (κ * R) *
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) :
    L < delta := by
  have hturn : 0 ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b :=
    m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 a b hab
  have hbase := m64Intrinsic_scaled_focusing_base_length_le_turning
    hR hκ hangle hL hturn hendpoint
  have hsmall : ∀ a b : ℝ, a ≤ b → b ≤ a + rampPeriod →
      intrinsicBoundaryLength N.metric 1 a b ≤ r →
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b <
          delta := by
    simpa only [IntrinsicAnnulus.SmallBoundaryTurning] using hturning
  exact lt_of_le_of_lt hbase (hsmall a b hab hperiod hsub)





theorem m64Intrinsic_jacobi_log_derivative_ge_cot_of_gaussian
    (N : IntrinsicAnnulus) (hK : N.GaussianCurvatureBound 1)
    {R : ℝ} (hR : 0 < R) (hRpi : R ≤ Real.pi)
    {q : ℝ → AnnulusCoordinates} {J J' J'' : ℝ → ℝ}
    (hmap : ∀ t ∈ Ioo (0 : ℝ) R, q t ∈ standardAnnulusDomain)
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 0)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 < J t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R,
      J'' t + (N.connection.scalarCurvature (q t) / 2) * J t = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) R) :
    Real.cos t / Real.sin t ≤ J' t / J t := by
  exact m64Intrinsic_jacobi_log_derivative_ge_cot hR hRpi hJ hJ' hJ'' hzero
    hpos hjac (fun s hs => hK (q s) (hmap s hs)) ht

end PoincareConjecture
