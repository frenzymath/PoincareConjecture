import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M46



def restrictUniformConstant {n : ℕ} {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} n taubar l0 V)
    (k : ℝ) (hk : 0 < k) (hkU : k ≤ U.kappa) :
    M15GeneralizedUniformData.{u} n taubar l0 V where
  taubar_pos := U.taubar_pos
  l₀_pos := U.l₀_pos
  V_pos := U.V_pos
  kappa := k
  kappa_pos := hk
  estimate := by
    intro X _ time I G T x E r J C _ _ _ _ _ B Q
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hkU (pow_nonneg B.radius_pos.le n))).trans
        (U.estimate X time I G T x E r J C B Q)



noncomputable def canonicalUniformData {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (kCan : ℝ) (hkCan : 0 < kCan) :
    M15GeneralizedUniformData.{u} 3 taubar l0 V :=
  restrictUniformConstant U (min U.kappa (8 * kCan))
    (lt_min U.kappa_pos (mul_pos (by norm_num) hkCan)) (min_le_left _ _)


theorem configurationKappa_le_canonical {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (kCan : ℝ) (hkCan : 0 < kCan) :
    configurationKappa p (canonicalUniformData U kCan hkCan) ≤ kCan := by
  apply (configurationKappa_le_uniform p _).trans
  change min U.kappa (8 * kCan) / 8 ≤ kCan
  have h := min_le_right U.kappa (8 * kCan)
  linarith

end PoincareConjecture.Proofs.M46
