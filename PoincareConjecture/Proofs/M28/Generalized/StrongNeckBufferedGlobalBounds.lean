import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedGlobalFlow
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedSourceBounds
import PoincareConjecture.Proofs.M28.Generalized.OrdinaryDerivativeRescaling










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
  (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8)



theorem GeneralizedStrongNeck.buffered_global_flow_curvatureTensorNorm
    (s : ℝ) (x : strongNeckOpen S) :
    ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).connection
      s).curvatureTensorNorm x =
      ((GeneralizedStrongNeck.rescaled_buffered_flow S H).connection
        (s / (Q * S.scale ^ 2))).curvatureTensorNorm x / (Q * S.scale ^ 2) := by
  have h := ((GeneralizedStrongNeck.buffered_global_rescaling
    S H Q hQ).metric_calculus s).curvature_norm_eq
      ((GeneralizedStrongNeck.rescaled_buffered_flow S H).connection
        (parabolicTimeInv (Q * S.scale ^ 2) 0 s))
      ((GeneralizedStrongNeck.buffered_global_rescaling S H Q hQ).flow.connection s) x
  have htime : parabolicTimeInv (Q * S.scale ^ 2) 0 s = s / (Q * S.scale ^ 2) := by
    simp only [parabolicTimeInv, zero_add]
  rw [htime] at h
  exact h



theorem GeneralizedStrongNeck.buffered_global_flow_curvatureDerivativeNorm
    (s : ℝ) (m : ℕ) (x : strongNeckOpen S) :
    ((GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow).connection
      s).curvatureDerivativeNorm m x =
      (Real.sqrt (Q * S.scale ^ 2))⁻¹ ^ (m + 2) *
        ((GeneralizedStrongNeck.rescaled_buffered_flow S H).connection
          (s / (Q * S.scale ^ 2))).curvatureDerivativeNorm m x := by
  have h := ordinaryRescaling_curvatureDerivativeNorm
    (GeneralizedStrongNeck.buffered_global_rescaling S H Q hQ) s m x
  have htime : parabolicTimeInv (Q * S.scale ^ 2) 0 s = s / (Q * S.scale ^ 2) := by
    simp only [parabolicTimeInv, zero_add]
  rw [htime] at h
  exact h




theorem exists_strongNeck_buffered_global_bounds_accuracy
    (hShi : LocalCurvatureDerivativeEstimates.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∃ K : ℝ, 0 < K ∧
        ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
          ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
            ∀ (F : GeneralizedRicciFlowData.{u}) (t : ℝ)
              (S : GeneralizedStrongNeck F t epsilon)
              (H : RescaledRawCylinderData (C := F.slice t)
                (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
                (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
              (Q : ℝ) (hQ : 0 < Q) (b : ℝ), 0 < b → b ≤ Q * S.scale ^ 2 →
              ∀ (tau : ℝ) (htau : 0 < tau)
                (hwindow : tau ≤ 5 * (Q * S.scale ^ 2) / 8),
                let G := GeneralizedStrongNeck.buffered_global_flow S H Q hQ tau htau hwindow
                (∀ s ∈ Icc (-tau) 0, ∀ x : strongNeckOpen S,
                  (G.connection s).curvatureTensorNorm x ≤ K / b) ∧
                ∀ m : ℕ, ∀ s ∈ Icc (-tau) 0, ∀ x : strongNeckOpen S,
                  |(S.coordinate_inverse x.val).2| ≤ 3 * epsilon⁻¹ / 4 →
                    (G.connection s).curvatureDerivativeNorm m x ≤
                      (Real.sqrt b)⁻¹ ^ (m + 2) * B m := by
  obtain ⟨epsilon0, hpos, hsmall, K, hK, hsource⟩ :=
    exists_strongNeck_buffered_source_bounds_accuracy hShi
  refine ⟨epsilon0, hpos, hsmall, K, hK, ?_⟩
  intro epsilon hepsilon heps
  obtain ⟨B, hB, hbounds⟩ := hsource epsilon hepsilon heps
  refine ⟨B, hB, ?_⟩
  intro F t S H Q hQ b hb hlower tau htau hwindow
  obtain ⟨hcurv, hderiv⟩ := hbounds F t S H
  have ha := GeneralizedStrongNeck.global_scale_pos S Q hQ
  constructor
  · intro s hs x
    have hcore := GeneralizedStrongNeck.buffered_global_time_mem S Q hQ hwindow hs
    have hbuffered : s / (Q * S.scale ^ 2) ∈ Icc (-(3 / 4 : ℝ)) 0 :=
      ⟨by linarith only [hcore.1], hcore.2⟩
    rw [GeneralizedStrongNeck.buffered_global_flow_curvatureTensorNorm]
    exact (div_le_div_of_nonneg_right (hcurv _ hbuffered x) ha.le).trans
      (div_le_div_of_nonneg_left hK.le hb hlower)
  · intro m s hs x hx
    have hcore := GeneralizedStrongNeck.buffered_global_time_mem S Q hQ hwindow hs
    have hfactor : (Real.sqrt (Q * S.scale ^ 2))⁻¹ ^ (m + 2) ≤
        (Real.sqrt b)⁻¹ ^ (m + 2) := by
      apply pow_le_pow_left₀ (by positivity)
      exact (inv_le_inv₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)).2
        (Real.sqrt_le_sqrt hlower)
    rw [GeneralizedStrongNeck.buffered_global_flow_curvatureDerivativeNorm]
    exact (mul_le_mul_of_nonneg_left (hderiv m _ hcore x hx)
      (by positivity)).trans (mul_le_mul_of_nonneg_right hfactor (hB m).le)

end PoincareConjecture.M28
