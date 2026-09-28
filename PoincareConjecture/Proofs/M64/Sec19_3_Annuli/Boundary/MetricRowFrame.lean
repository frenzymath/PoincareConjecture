import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryGeometry











noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Complex
open scoped ContDiff

namespace PoincareConjecture.M64

open M65Branch

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)





def metricRowFrame (G : E →L[ℝ] E →L[ℝ] ℝ) (V : E) (j : Fin n) : E →L[ℝ] E :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k => if k = j then G V else
      EuclideanSpace.proj k - (V k / V j) • EuclideanSpace.proj j)





theorem metricRowFrame_apply (G : E →L[ℝ] E →L[ℝ] ℝ) (V W : E) (j k : Fin n) :
    metricRowFrame G V j W k = if k = j then G V W else W k - (V k / V j) * W j := by
  simp only [metricRowFrame, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_apply,
    ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl





theorem metricRowFrame_injective (G : E →L[ℝ] E →L[ℝ] ℝ)
    (V : E) (j : Fin n) (hV : V j ≠ 0)
    (hpos : ∀ W : E, W ≠ 0 → 0 < G W W) : Function.Injective (metricRowFrame G V j) := by
  have hzero (W : E) (hW : metricRowFrame G V j W = 0) : W = 0 := by
    have hrows (k : Fin n) : (if k = j then G V W else W k - (V k / V j) * W j) = 0 := by
      rw [← metricRowFrame_apply]
      exact congrArg (fun X : E => X k) hW
    have hform : W = (W j / V j) • V := by
      ext k
      change W k = (W j / V j) * V k
      by_cases hk : k = j
      · subst k
        exact (div_mul_cancel₀ (W j) hV).symm
      · have h := hrows k
        rw [if_neg hk] at h
        linear_combination h
    have hV0 : V ≠ 0 := fun h => hV (by rw [h]; rfl)
    have hG : G V W = 0 := by simpa using hrows j
    rw [hform, map_smul, smul_eq_mul] at hG
    have ha : W j / V j = 0 := (mul_eq_zero.mp hG).resolve_right (hpos V hV0).ne'
    rw [hform, ha, zero_smul]
  intro W Z heq
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, heq, sub_self]





theorem metricRowFrame_contDiffOn
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {V : E → E} {U : Set E} (j : Fin n)
    (hG : ContDiffOn ℝ ∞ G U) (hV : ContDiffOn ℝ ∞ V U)
    (hj : ∀ q ∈ U, V q j ≠ 0) :
    ContDiffOn ℝ ∞ (fun q => metricRowFrame (G q) (V q) j) U := by
  apply contDiffOn_clm_apply.mpr
  intro W
  have hv (k : Fin n) : ContDiffOn ℝ ∞ (fun q => V q k) U :=
    (EuclideanSpace.proj k : E →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hrows : ContDiffOn ℝ ∞
      (fun q => fun k : Fin n => if k = j then G q (V q) W else
        W k - (V q k / V q j) * W j) U := by
    apply contDiffOn_pi.mpr
    intro k
    by_cases hk : k = j
    · simpa only [if_pos hk] using (hG.clm_apply hV).clm_apply contDiffOn_const
    · convert! (contDiffOn_const (c := W k)).sub
        (((hv k).div (hv j) hj).mul (contDiffOn_const (c := W j))) using 1
      funext q
      simp only [if_neg hk]
      rfl
  have h := (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.comp_contDiffOn hrows
  apply h.congr
  intro q _
  ext k
  exact metricRowFrame_apply (G q) (V q) W j k





theorem metricRowFrame_complex_isUnit (G : E →L[ℝ] E →L[ℝ] ℝ)
    (V : E) (j : Fin n) (hV : V j ≠ 0)
    (hpos : ∀ W : E, W ≠ 0 → 0 < G W W) :
    IsUnit (complexifyOperator (metricRowFrame G V j)) := by
  have hi := M65StrictTrace.complexifyOperator_injective (metricRowFrame G V j)
    (metricRowFrame_injective G V j hV hpos)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩

end PoincareConjecture.M64
