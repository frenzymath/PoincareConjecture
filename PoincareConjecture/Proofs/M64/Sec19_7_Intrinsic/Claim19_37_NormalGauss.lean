import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_InitialDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CovariantPullback

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open ConnectionAlongCurve ConnectionVariation CoordinateExponential RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_jacobi_preserves_normality
    (N : IntrinsicAnnulus) {q X : ℝ → AnnulusCoordinates} {I : Set ℝ} {b : ℝ}
    (hb : 0 < b) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ q I)
    (hgeo : N.metric.IsGeodesicOn q I) (hsub : Icc (0 : ℝ) b ⊆ I)
    (hX : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) X) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) b,
      manifoldCovDerivAlong N.metric q (manifoldCovDerivAlong N.metric q X 1) 1 t =
        -N.connection.curvature (q t) (X t)
          (curveVelocity (n := 2) q t) (curveVelocity (n := 2) q t))
    (horth : N.metric.inner (q 0) (curveVelocity (n := 2) q 0) (X 0) = 0)
    (hDorth : N.metric.inner (q 0) (curveVelocity (n := 2) q 0)
      (manifoldCovDerivAlong N.metric q X 1 0) = 0) :
    ∀ t ∈ Icc (0 : ℝ) b,
      N.metric.inner (q t) (curveVelocity (n := 2) q t) (X t) = 0 := by
  let V : ℝ → AnnulusCoordinates := fun t => curveVelocity (n := 2) q t
  let A : ℝ → ℝ := fun t => N.metric.inner (q t) (V t)
    (manifoldCovDerivAlong N.metric q X 1 t)
  let B : ℝ → ℝ := fun t => N.metric.inner (q t) (V t) (X t)
  have hz : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hV (t : ℝ) (ht : t ∈ I) : ContDiffAt ℝ ∞ (chartField q (q t) V) t :=
    contDiffAt_chartField_velocity hI hq ht (mem_extChartAt_source _)
  have hDV (t : ℝ) (ht : t ∈ I) : manifoldCovDerivAlong N.metric q V 1 t = 0 :=
    hgeo.manifoldCovDeriv_velocity_eq_zero hI hq ht
  have hA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) : HasDerivAt A 0 t := by
    have h := hasDerivAt_metric_inner_along N.metric
      (hq.contMDiffAt (hI.mem_nhds (hsub ht))) (hV t (hsub ht))
      (contDiffAt_chartField_covDeriv N.metric hI hq hX (hsub ht) (mem_extChartAt_source _))
    change HasDerivAt A
      (N.metric.inner (q t) (manifoldCovDerivAlong N.metric q V 1 t)
        (manifoldCovDerivAlong N.metric q X 1 t) +
        N.metric.inner (q t) (V t)
          (manifoldCovDerivAlong N.metric q (manifoldCovDerivAlong N.metric q X 1) 1 t)) t at h
    rw [hDV t (hsub ht), hjac t ht, map_zero, zero_apply, zero_add, map_neg] at h
    have hskew := N.connection.curvatureTensor_swap_last (q t) (X t) (V t) (V t) (V t)
    have hcurv : N.metric.inner (q t) (V t)
        (N.connection.curvature (q t) (X t) (V t) (V t)) = 0 := by
      rw [N.metric.symm]
      change N.connection.curvatureTensor (q t) (X t) (V t) (V t) (V t) = 0
      linarith
    simpa only [V, hcurv, neg_zero] using h
  have hAzero (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) : A t = 0 := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hA s hs).hasDerivWithinAt)
      (C := 0) (fun _ _ => by simp) (convex_Icc (0 : ℝ) b) hz ht
    have hA0 : A 0 = 0 := hDorth
    simpa only [hA0, sub_zero, zero_mul, norm_le_zero_iff] using h
  have hB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) : HasDerivAt B 0 t := by
    have h := hasDerivAt_metric_inner_along N.metric
      (hq.contMDiffAt (hI.mem_nhds (hsub ht))) (hV t (hsub ht)) (hX t (hsub ht))
    change HasDerivAt B
      (N.metric.inner (q t) (manifoldCovDerivAlong N.metric q V 1 t) (X t) + A t) t at h
    simpa only [hDV t (hsub ht), map_zero, zero_apply, zero_add, hAzero t ht] using h
  intro t ht
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hB s hs).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) (convex_Icc (0 : ℝ) b) hz ht
  have hB0 : B 0 = 0 := horth
  simpa only [hB0, sub_zero, zero_mul, norm_le_zero_iff] using h

theorem m64Intrinsic_boundary_normal_derivative_orthogonal
    (N : IntrinsicAnnulus) {radius : ℝ} {normal : ℝ → AnnulusCoordinates}
    (hnormal : ContDiff ℝ ∞ normal)
    (hunit : ∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s)
      (normal s) (normal s) = 1) (a : ℝ) :
    N.metric.inner (intrinsicAnnulusBoundary radius a) (normal a)
      (rampHorizontalCovariantDerivative N.connection
        (intrinsicAnnulusBoundary radius) normal a) = 0 := by
  have hgamma := m64Intrinsic_contDiff_boundary radius
  have hfield := m64Intrinsic_mdifferentiable_tangent_field
    (x := a) hgamma.contDiffAt hnormal.contDiffAt
  have h := M62.hasDerivAt_metric_pairing N.connection (x := a)
    ((contMDiff_iff_contDiff.mpr hgamma).mdifferentiableAt (by simp)) hfield hfield
  have heq : (fun s => N.metric.inner (intrinsicAnnulusBoundary radius s)
      (normal s) (normal s)) = fun _ => (1 : ℝ) := funext hunit
  rw [heq] at h
  have hz := h.unique (hasDerivAt_const a (1 : ℝ))
  rw [N.metric.symm] at hz
  linarith

theorem m64Intrinsic_normal_variation_orthogonal
    (N : IntrinsicAnnulus) {radius : ℝ}
    {u : ℝ × ℝ → AnnulusCoordinates} {S I : Set ℝ}
    (hS : IsOpen S) (hI : IsOpen I)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (S ×ˢ I))
    (hgeo : ∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I)
    (hboundary : ∀ s ∈ S, u (s, 0) = intrinsicAnnulusBoundary radius s)
    {normal : ℝ → AnnulusCoordinates} (hnormal : ContDiff ℝ ∞ normal)
    (hunit : ∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s)
      (normal s) (normal s) = 1)
    (horth : ∀ s, N.metric.inner (intrinsicAnnulusBoundary radius s) (normal s)
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) s) = 0)
    (hvelocity : ∀ s ∈ S, curveVelocity (n := 2) (fun t => u (s, t)) 0 = normal s)
    {a b : ℝ} (ha : a ∈ S) (hb : 0 < b) (hsub : Icc (0 : ℝ) b ⊆ I) :
    ∀ t ∈ Icc (0 : ℝ) b,
      N.metric.inner (u (a, t)) (curveVelocity (n := 2) (fun r => u (a, r)) t)
        (curveVelocity (n := 2) (fun s => u (s, t)) a) = 0 := by
  have hz : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, hb.le⟩
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun t => u (a, t)) I := by
    intro t ht
    exact ((hu.contMDiffAt ((hS.prod hI).mem_nhds ⟨ha, ht⟩)).comp t
      (show ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun r => (a, r)) t from
        contMDiffAt_iff_contDiffAt.mpr (by fun_prop))).contMDiffWithinAt
  apply m64Intrinsic_jacobi_preserves_normality N hb hI hq (hgeo a ha) hsub
  · intro t ht
    rw [m64Intrinsic_chartField_eq]
    exact m64Intrinsic_contDiff_variation_field hS hI hu.contDiffOn ha ht
  · intro t ht
    exact m64Intrinsic_variation_intrinsic_jacobi N hS hI hu hgeo ha (hsub ht)
  · have heq : (fun s => u (s, 0)) =ᶠ[𝓝 a] intrinsicAnnulusBoundary radius := by
      filter_upwards [hS.mem_nhds ha] with s hs
      exact hboundary s hs
    have hX0 : curveVelocity (n := 2) (fun s => u (s, 0)) a =
        curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) a := by
      rw [m64Intrinsic_curveVelocity_eq_deriv, m64Intrinsic_curveVelocity_eq_deriv]
      exact heq.deriv_eq
    erw [hvelocity a ha, hX0, hboundary a ha]
    exact horth a
  · have hD := m64Intrinsic_normal_variation_initial_covDeriv N hS hI (hsub hz) hu
      hboundary hnormal hvelocity ha
    rw [hD]
    erw [hvelocity a ha, hboundary a ha]
    exact m64Intrinsic_boundary_normal_derivative_orthogonal N hnormal hunit a

end PoincareConjecture
