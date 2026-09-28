import PoincareConjecture.Proofs.M32.Claim11_32.Worldlines.Maximal
import PoincareConjecture.Proofs.M32.Cor11_36.Restriction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

theorem strongNeck_maximalBackwardFlowLine {F : GeneralizedRicciFlowData.{u}}
    {t epsilon : ℝ} (N : GeneralizedStrongNeck F t epsilon)
    {q mu : ℝ} (hq : 0 < q) (_hmu : 0 < mu) (hmu1 : mu < 1) :
    Nonempty (GeneralizedMaximalBackwardFlowLine F ⟨t, N.center⟩ q
      (mu * q / max q ((F.connection t).scalarCurvature N.center))) := by
  let R := (F.connection t).scalarCurvature N.center
  have hR : 0 < R := N.scalar_center_pos
  have hscale : N.scale = (Real.sqrt R)⁻¹ := by
    rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, Real.sqrt_eq_rpow]
  have hr : N.scale⁻¹ ^ 2 = R := by
    rw [hscale, inv_inv, Real.sq_sqrt hR.le]
  let e := restrictCylinderSpace N.time_cylinder
    (singleton_subset_iff.mpr (N.central_sphere_subset N.center_on_central_sphere))
  apply maximalBackwardFlowLine_of_rescaled_cylinder e ordConnected_Ioc
    (show (0 : ℝ) ∈ Ioc (-1) 0 by norm_num)
    (N.cylinder_identity _ _ (N.central_sphere_subset N.center_on_central_sphere)) hq
  intro s hs
  rw [hr]
  have hm : 0 < max q R := lt_of_lt_of_le hq (le_max_left _ _)
  have hduration : (mu * q / max q R) * R < q := by
    have hmul : mu * R < max q R :=
      (mul_lt_of_lt_one_left hR hmu1).trans_le (le_max_right _ _)
    calc
      (mu * q / max q R) * R = (mu * R / max q R) * q := by ring
      _ < 1 * q := mul_lt_mul_of_pos_right ((div_lt_iff₀ hm).mpr (by simpa using hmul)) hq
      _ = q := one_mul q
  refine ⟨(lt_div_iff₀ hq).mpr ?_, div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hs.2 hR.le) hq.le⟩
  have hlow := mul_le_mul_of_nonneg_right hs.1 hR.le
  dsimp only [R] at hduration hlow ⊢
  linarith

theorem maximalBackwardFlowLineSurvival_of_strongNecks
    (S : GeneralizedBlowupSequence.{u}) {mu epsilon : ℝ}
    (hmu : 0 < mu) (hmu1 : mu < 1)
    (hnecks : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
      ∀ x ∈ S.baseBall k A,
        ∃ N : GeneralizedStrongNeck (S.flow k) (S.base k).1 epsilon, N.center = x) :
    GeneralizedMaximalBackwardFlowLineSurvival S mu := by
  intro A hA
  filter_upwards [hnecks A hA] with k hk
  intro x hx
  obtain ⟨N, rfl⟩ := hk x hx
  exact strongNeck_maximalBackwardFlowLine N (S.base_scalar_pos k) hmu hmu1

end PoincareConjecture.M32
