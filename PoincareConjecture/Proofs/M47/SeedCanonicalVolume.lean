import PoincareConjecture.Proofs.M47.SeedVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem canonical_seed_volume_or_component (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {t rho r : ℝ} {x : (F.slice t).carrier}
    (hcanonical : SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 200)
    (hhigh : rho⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x)
    (hpinch : SurgeryPinchedAt (F.connection t) t)
    (hr : 0 < r) (hscalar : (F.connection t).scalarCurvature x ≤ 9 * r⁻¹ ^ 2) :
    ENNReal.ofReal (canonicalSeedDensity F.parameters.C * r ^ 3) ≤
      calibratedMetricVolume (F.metric t) ((F.metric t).ball x r) ∨
    (∃ N : SingularCComponent (F.metric t) (F.connection t) F.parameters.C,
      x ∈ N.carrier) ∨
    ∃ N : SingularRoundComponent (F.metric t) F.parameters.epsilon, x ∈ N.carrier := by
  cases hcanonical with
  | neck N hx =>
    left
    have hNscalar : N.neck.connection.scalarCurvature N.neck.center ≤ 9 * r⁻¹ ^ 2 := by
      rw [N.connection_eq, hx]
      exact hscalar
    have hscale := M46.canonicalNeck_scale_of_scalar_bound N.neck hr hNscalar
    have hvolume := M46.canonicalNeck_test_ball_volume N.neck hr hscale
    rw [hx] at hvolume
    rw [M15.calibratedMetricVolume_eq_volumeMeasure]
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_left _ _) (pow_nonneg hr.le 3))).trans hvolume
  | cap N _hEpsilon hC hconnection hx =>
    left
    have hNhigh : rho⁻¹ ^ 2 ≤ N.connection.scalarCurvature x := by
      rw [hconnection]
      exact hhigh
    have hsmall : N.core_radius x ≤ 1 / 200 :=
      (M46.canonicalCap_core_radius_le N hx hrho hNhigh).trans hrhoSmall
    have hNpinch : SurgeryPinchedAt N.connection t := by
      rw [hconnection]
      exact hpinch
    have hNscalar : N.connection.scalarCurvature x ≤ 9 * r⁻¹ ^ 2 := by
      rw [hconnection]
      exact hscalar
    have hvolume := M46.canonicalCap_test_ball_volume P.toM46 N hx
      (le_max_left 1 F.parameters.C) (hC.trans (le_max_right _ _)) hr
      hNpinch hsmall hNscalar
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (min_le_right _ _) (pow_nonneg hr.le 3))).trans hvolume
  | component N hx => exact Or.inr (Or.inl ⟨N, hx⟩)
  | round N hx => exact Or.inr (Or.inr ⟨N, hx⟩)

theorem canonical_test_volume_or_component (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {t rho r : ℝ} {x : (F.slice t).carrier}
    (hcanonical : SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 200)
    (hhigh : rho⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x)
    (hpinch : SurgeryPinchedAt (F.connection t) t) (hr : 0 < r)
    (e : SurgeryFlowCylinder F (F.slice t) t 1 (Icc (-r ^ 2) 0)
      ((F.metric t).ball x r))
    (hbased : ∀ hs y, y ∈ (F.metric t).ball x r → HEq (e.forward 0 hs y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric t).ball x r →
      (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (canonicalSeedDensity F.parameters.C * r ^ 3) ≤
      calibratedMetricVolume (F.metric t) ((F.metric t).ball x r) ∨
    (∃ N : SingularCComponent (F.metric t) (F.connection t) F.parameters.C,
      x ∈ N.carrier) ∨
    ∃ N : SingularRoundComponent (F.metric t) F.parameters.epsilon, x ∈ N.carrier := by
  have hzero : (0 : ℝ) ∈ Icc (-r ^ 2) 0 := ⟨neg_nonpos.mpr (sq_nonneg r), le_rfl⟩
  have hx : x ∈ (F.metric t).ball x r := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) x x < ENNReal.ofReal r
    simpa only [Manifold.riemannianEDist_self] using ENNReal.ofReal_pos.mpr hr
  have hpoint : (⟨t + 0 / 1, e.forward 0 hzero x⟩ :
      (s : ℝ) × (F.slice s).carrier) = ⟨t, x⟩ :=
    Sigma.ext (by simp) (hbased hzero x hx)
  have hread := congrArg (fun q : (s : ℝ) × (F.slice s).carrier =>
    (F.connection q.1).curvatureTensorNorm q.2) hpoint
  have hterminal : (F.connection t).curvatureTensorNorm x ≤ r⁻¹ ^ 2 :=
    hread ▸ hcurv 0 hzero x hx
  have hscalar := (le_abs_self _).trans
    (M10.abs_scalarCurvature_le (F.metric t) (F.connection t) x)
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] at hscalar
  exact canonical_seed_volume_or_component P hcanonical hrho hrhoSmall hhigh hpinch hr
    (hscalar.trans (mul_le_mul_of_nonneg_left hterminal (by norm_num)))

end PoincareConjecture.Proofs.M47
