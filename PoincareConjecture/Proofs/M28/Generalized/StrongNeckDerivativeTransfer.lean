import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalShiHomothetyCurvature
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricCurvatureNaturality
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSourceBounds











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

private theorem homothety_norm_factor {Q : ℝ} (hQ : 0 < Q) (m : ℕ) :
    Q * (Real.sqrt Q)⁻¹ ^ (4 + m) = (Real.sqrt Q)⁻¹ ^ (m + 2) := by
  have hs : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  rw [show 4 + m = 2 + (m + 2) by omega, pow_add]
  have hcancel : Q * (Real.sqrt Q)⁻¹ ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hQ.le, mul_inv_cancel₀ hQ.ne']
  rw [← mul_assoc, hcancel, one_mul]



theorem GeneralizedStrongNeck.scaled_curvatureDerivativeNorm
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (H : RescaledRawCylinderData (C := F.slice t)
      (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
      (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
    (Q : ℝ) (hQ : 0 < Q)
    (D : LeviCivitaData (M13.scaleSmoothMetric (F.metric t) Q hQ))
    (m : ℕ) (x : strongNeckOpen S) :
    D.curvatureDerivativeNorm m x.val =
      (Real.sqrt (Q * S.scale ^ 2))⁻¹ ^ (m + 2) *
        (H.rescaling.flow.connection 0).curvatureDerivativeNorm m x := by
  let G := H.rescaling.flow.metric 0
  let DG := H.rescaling.flow.connection 0
  let a := Q * S.scale ^ 2
  have ha : 0 < a := mul_pos hQ (sq_pos_of_pos S.scale_pos)
  let DA := M13.scaleLeviCivitaData DG a ha
  have hinv : ∀ y : strongNeckOpen S, y ∈ (univ : Set (strongNeckOpen S)) →
      (mfderiv (𝓡 3) (𝓡 3)
        (Subtype.val : strongNeckOpen S → (F.slice t).carrier) y).IsInvertible := by
    intro y _
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hmetric : ∀ y : strongNeckOpen S, y ∈ (univ : Set (strongNeckOpen S)) →
      ∀ v w : TangentSpace (𝓡 3) y,
      (M13.scaleSmoothMetric G a ha).inner y v w =
        (M13.scaleSmoothMetric (F.metric t) Q hQ).inner y.val
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) y v)
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) y w) := by
    intro y _ v w
    rw [M13.scaleSmoothMetric_inner, M13.scaleSmoothMetric_inner]
    dsimp only [G]
    rw [GeneralizedStrongNeck.rescaled_metric_at_zero S H]
    dsimp only [a]
    have hs : S.scale ≠ 0 := S.scale_pos.ne'
    field_simp
  have hlocal := DA.curvatureDerivativeNorm_eq_pullback D isOpen_univ
    contMDiff_subtype_val.contMDiffOn hinv hmetric m (mem_univ x)
  rw [← hlocal, scale_curvatureDerivativeNorm_eq G DG a ha m x,
    homothety_norm_factor ha m]



theorem inverse_sqrt_le_of_normalized_scalar
    {a R K : ℝ} (ha : 0 < a) (hnormalized : a * R = 1) (hR : R ≤ K) :
    (Real.sqrt a)⁻¹ ≤ max K 1 := by
  have hsq : ((Real.sqrt a)⁻¹) ^ 2 = R := by
    rw [inv_pow, Real.sq_sqrt ha.le]
    exact inv_eq_of_mul_eq_one_right (by simpa only [mul_comm] using hnormalized)
  have hbound : ((Real.sqrt a)⁻¹) ^ 2 ≤ max K 1 :=
    (hsq ▸ hR).trans (le_max_left _ _)
  have hone : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  nlinarith [sq_nonneg ((Real.sqrt a)⁻¹ - max K 1)]

end PoincareConjecture.M28
