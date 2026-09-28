import PoincareConjecture.Proofs.M28.Generalized.StrongNeckGlobalFlow
import PoincareConjecture.Proofs.M28.Generalized.OrdinaryDerivativeRescaling
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckQuarterBounds
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckTerminalBalls











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
  (Q : ℝ) (hQ : 0 < Q) (tau : ℝ) (htau : 0 < tau)
  (hwindow : tau ≤ Q * S.scale ^ 2 / 4)



theorem GeneralizedStrongNeck.global_flow_curvatureTensorNorm
    (s : ℝ) (x : strongNeckOpen S) :
    ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection
      s).curvatureTensorNorm x =
      ((GeneralizedStrongNeck.rescaled_half_flow S H).connection
        (s / (Q * S.scale ^ 2))).curvatureTensorNorm x / (Q * S.scale ^ 2) := by
  have h := ((GeneralizedStrongNeck.global_rescaling S H Q hQ).metric_calculus s).curvature_norm_eq
      ((GeneralizedStrongNeck.rescaled_half_flow S H).connection
        (parabolicTimeInv (Q * S.scale ^ 2) 0 s))
      ((GeneralizedStrongNeck.global_rescaling S H Q hQ).flow.connection s) x
  have htime : parabolicTimeInv (Q * S.scale ^ 2) 0 s = s / (Q * S.scale ^ 2) := by
    simp only [parabolicTimeInv, zero_add]
  rw [htime] at h
  exact h



theorem GeneralizedStrongNeck.global_flow_curvatureDerivativeNorm
    (s : ℝ) (m : ℕ) (x : strongNeckOpen S) :
    ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection
      s).curvatureDerivativeNorm m x =
      (Real.sqrt (Q * S.scale ^ 2))⁻¹ ^ (m + 2) *
        ((GeneralizedStrongNeck.rescaled_half_flow S H).connection
          (s / (Q * S.scale ^ 2))).curvatureDerivativeNorm m x := by
  have h := ordinaryRescaling_curvatureDerivativeNorm
    (GeneralizedStrongNeck.global_rescaling S H Q hQ) s m x
  have htime : parabolicTimeInv (Q * S.scale ^ 2) 0 s = s / (Q * S.scale ^ 2) := by
    simp only [parabolicTimeInv, zero_add]
  rw [htime] at h
  exact h






theorem exists_strongNeck_global_bounds_accuracy
    (hShi : LocalCurvatureDerivativeEstimates.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∃ K : ℝ, 0 < K ∧
        ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
          ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
            ∀ (F : GeneralizedRicciFlowData.{u}) (t : ℝ)
              (S : GeneralizedStrongNeck F t epsilon)
              (H : RescaledRawCylinderData (C := F.slice t)
                (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
                (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
              (Q : ℝ) (hQ : 0 < Q) (b : ℝ), 0 < b → b ≤ Q * S.scale ^ 2 →
              ∀ (tau : ℝ) (htau : 0 < tau)
                (hwindow : tau ≤ Q * S.scale ^ 2 / 4),
                let G := GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow
                (∀ s ∈ Icc (-tau) 0, ∀ x : strongNeckOpen S,
                  (G.connection s).curvatureTensorNorm x ≤ K / b) ∧
                ∀ m : ℕ, ∀ s ∈ Icc (-tau) 0, ∀ x : strongNeckOpen S,
                  x.val ∈ (F.metric t).ball S.center (S.scale * (epsilon⁻¹ / 16)) →
                    (G.connection s).curvatureDerivativeNorm m x ≤
                      (Real.sqrt b)⁻¹ ^ (m + 2) * B m := by
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, hsource⟩ :=
    exists_strongNeck_source_quarter_bounds_accuracy hShi
  refine ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, ?_⟩
  intro epsilon hepsilon hsmall
  obtain ⟨B, hB, hbound⟩ := hsource epsilon hepsilon hsmall
  refine ⟨B, hB, ?_⟩
  intro F t S H Q hQ b hb hlower tau htau hwindow
  obtain ⟨hcurv, hderiv⟩ := hbound F t S H
  have ha := GeneralizedStrongNeck.global_scale_pos S Q hQ
  constructor
  · intro s hs x
    have hquarter := GeneralizedStrongNeck.global_time_mem_quarter S Q hQ hwindow hs
    have hhalf : s / (Q * S.scale ^ 2) ∈ Icc (-(1 / 2 : ℝ)) 0 :=
      ⟨by linarith [hquarter.1], hquarter.2⟩
    rw [GeneralizedStrongNeck.global_flow_curvatureTensorNorm]
    exact (div_le_div_of_nonneg_right (hcurv _ hhalf x) ha.le).trans
      (div_le_div_of_nonneg_left hK.le hb hlower)
  · intro m s hs x hx
    have hquarter := GeneralizedStrongNeck.global_time_mem_quarter S Q hQ hwindow hs
    have hepshalf : epsilon < 1 / 2 :=
      lt_of_le_of_lt (hsmall.trans hthreshold) (by norm_num)
    have hball : x ∈ ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        (strongNeckSourceCenter S) (epsilon⁻¹ / 16) := by
      rw [GeneralizedStrongNeck.rescaled_half_ball_eq_preimage S H hepshalf
        (by nlinarith [inv_pos.mpr hepsilon] : epsilon⁻¹ / 16 ≤ epsilon⁻¹ / 8)]
      exact hx
    have hfactor : (Real.sqrt (Q * S.scale ^ 2))⁻¹ ^ (m + 2) ≤
        (Real.sqrt b)⁻¹ ^ (m + 2) := by
      apply pow_le_pow_left₀ (by positivity)
      exact (inv_le_inv₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)).2
        (Real.sqrt_le_sqrt hlower)
    rw [GeneralizedStrongNeck.global_flow_curvatureDerivativeNorm]
    exact (mul_le_mul_of_nonneg_left (hderiv m _ hquarter x hball)
      (by positivity)).trans (mul_le_mul_of_nonneg_right hfactor (hB m).le)

end PoincareConjecture.M28
