import PoincareConjecture.Proofs.M28.Generalized.StrongNeckNormalizedFlow
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSlice
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M13.ContractionTransport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

def strongNeckOpen {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    TopologicalSpace.Opens (F.slice t).carrier :=
  ⟨S.carrier, S.carrier_open⟩

theorem GeneralizedStrongNeck.rescaled_metric_at_zero
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (H : RescaledRawCylinderData (C := F.slice t)
      (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
      (strongNeckCylinder S) (physical_interval_subset S))
    (x : strongNeckOpen S)
    (v w : TangentSpace (𝓡 3) x) :
    (H.rescaling.flow.metric 0).inner x v w =
      S.scale⁻¹ ^ 2 * (F.metric t).inner x.1
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          x w) := by
  have hq : 0 < S.scale⁻¹ ^ 2 :=
    sq_pos_of_pos (inv_pos.mpr S.scale_pos)
  have hJ0 : (0 : ℝ) ∈ strongNeckBackwardInterval.domain := by
    exact ⟨by norm_num, le_rfl⟩
  let K := Proofs.M12.cylinderPhysicalInterval t (S.scale⁻¹ ^ 2)
    S.time_cylinder.scale_pos strongNeckBackwardInterval
  have hKt : t ∈ K.domain := by
    change ∃ r, r ∈ strongNeckBackwardInterval.domain ∧
      parabolicTimeInv (S.scale⁻¹ ^ 2) t r = t
    refine ⟨0, hJ0, ?_⟩
    simp [parabolicTimeInv]
  have hP0 : (0 : ℝ) ∈
      (parabolicInterval (S.scale⁻¹ ^ 2) hq t K).domain := by
    apply (mem_parabolicInterval_iff (S.scale⁻¹ ^ 2) hq t K 0).2
    simpa [parabolicTimeInv] using hKt
  let z0 : (parabolicInterval (S.scale⁻¹ ^ 2) hq t K).domain :=
    ⟨0, hP0⟩
  have hmetric := rescaled_pullback_metric_eq
    (e := strongNeckCylinder S) (hI := physical_interval_subset S) H z0 x v w
  have hzval :
      (rescaledTime (U := strongNeckOpen S) (strongNeckCylinder S) z0).val = 0 := by
    simp [z0]
  have hmetric0 :
      (H.rescaling.flow.metric 0).inner x v w =
        (strongNeckCylinder S).pullbackInner 0 hJ0 x.1
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x w) := by
    simpa only [hzval] using hmetric
  have hforward : ∀ y : (F.slice t).carrier,
      (strongNeckCylinder S).forward 0 hJ0 y =
        S.time_cylinder.forward 0 hJ0 y := by
    intro y
    simp [strongNeckCylinder]
  have hidentity : ∀ y ∈ S.carrier,
      (⟨t + 0 / S.scale⁻¹ ^ 2,
        (strongNeckCylinder S).forward 0 hJ0 y⟩ : F.point) = ⟨t, y⟩ := by
    intro y hy
    rw [hforward]
    simpa only [GeneralizedFlowCylinder.pointMap, strongNeckCylinder] using
      S.cylinder_identity hJ0 y hy
  have hslice := slice_pullback_eq_of_identity F (by simp) S.carrier_open
    ((strongNeckCylinder S).forward 0 hJ0) hidentity (x := x.1) x.2
    (mfderiv (𝓡 3) (𝓡 3)
      (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x v)
    (mfderiv (𝓡 3) (𝓡 3)
      (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x w)
  calc
    (H.rescaling.flow.metric 0).inner x v w =
        (strongNeckCylinder S).pullbackInner 0 hJ0 x.1
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3)
            (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x w) := by
      exact hmetric0
    _ = S.scale⁻¹ ^ 2 * (F.metric t).inner x.1
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : strongNeckOpen S → (F.slice t).carrier) x w) := by
      simp only [GeneralizedFlowCylinder.pullbackInner]
      rw [hslice]

theorem GeneralizedStrongNeck.rescaled_scalar_at_center
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (H : RescaledRawCylinderData (C := F.slice t)
      (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
      (strongNeckCylinder S) (physical_interval_subset S)) :
    (H.rescaling.flow.connection 0).scalarCurvature
        ⟨S.center, S.central_sphere_subset S.center_on_central_sphere⟩ = 1 := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckOpen S) :=
    @TopologicalSpace.Opens.instChartedSpace _ _ _ _
      (F.slice t).chartedSpace (strongNeckOpen S)
  let q : ℝ := S.scale⁻¹ ^ 2
  have hq : 0 < q := by
    dsimp [q]
    exact sq_pos_of_pos (inv_pos.mpr S.scale_pos)
  let g₀ : RiemannianMetric 3 (strongNeckOpen S) :=
    H.rescaling.flow.metric 0
  let g₁ : RiemannianMetric 3 (F.slice t).carrier :=
    M13.scaleSmoothMetric (F.metric t) q hq
  let D₀ : LeviCivitaData g₀ := H.rescaling.flow.connection 0
  let D₁ : LeviCivitaData g₁ :=
    M13.scaleLeviCivitaData (F.connection t) q hq
  have hmetric : ∀ y : strongNeckOpen S, y ∈ (Set.univ : Set (strongNeckOpen S)) →
      ∀ a b : TangentSpace (𝓡 3) y,
        g₀.inner y a b =
          g₁.inner y.1
            (mfderiv (𝓡 3) (𝓡 3)
              (Subtype.val : strongNeckOpen S → (F.slice t).carrier) y a)
            (mfderiv (𝓡 3) (𝓡 3)
              (Subtype.val : strongNeckOpen S → (F.slice t).carrier) y b) := by
    intro y hy a b
    have hm := GeneralizedStrongNeck.rescaled_metric_at_zero S H y a b
    simpa [g₀, g₁, q, M13.scaleSmoothMetric_inner] using hm
  let xc : strongNeckOpen S :=
    ⟨S.center, S.central_sphere_subset S.center_on_central_sphere⟩
  have hlocal : D₀.scalarCurvature xc = D₁.scalarCurvature xc.1 := by
    exact D₀.scalarCurvature_eq_of_local_isometry D₁ isOpen_univ
      contMDiff_subtype_val.contMDiffOn hmetric (mem_univ xc)
  have hhom := M13.homothety_scalarCurvature_eq
    (F.metric t) g₁ (Diffeomorph.refl (𝓡 3) (F.slice t).carrier ∞)
    q hq (M13.identity_metricHomothety (F.metric t) q hq)
    (F.connection t) D₁ xc.1
  have hscale : S.scale⁻¹ ^ 2 =
      (F.connection t).scalarCurvature S.center := by
    rw [S.scale_scalar, inv_pow,
      ← Real.rpow_mul_natCast S.scalar_center_pos.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  calc
    (H.rescaling.flow.connection 0).scalarCurvature xc =
        D₀.scalarCurvature xc := rfl
    _ = D₁.scalarCurvature xc.1 := hlocal
    _ = (F.connection t).scalarCurvature S.center / q := by
      simpa [D₁, g₁, xc] using hhom
    _ = 1 := by
      change (F.connection t).scalarCurvature S.center /
        (S.scale⁻¹ ^ 2) = 1
      rw [hscale]
      exact div_self (ne_of_gt S.scalar_center_pos)

end PoincareConjecture.M28
