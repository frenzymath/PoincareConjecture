import PoincareConjecture.Proofs.M35.CapGeometry.RadialLocalScalar
import PoincareConjecture.Proofs.M35.CapGeometry.RadialIntervals
import PoincareConjecture.Proofs.M35.CapGeometry.GuardedScalarFloor










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single 2 1




theorem axisWarpingRadius_mul_sqrt_scalar_le
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hsec : D.NonnegativeSectionalCurvature) (hcomplete : MetricComplete g)
    (hpos : ∀ x, 0 < D.scalarCurvature x)
    (hreg : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature)
    {A H : ℝ} (hA : 0 < A)
    (hgrad : ∀ x, H ≤ D.scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
        |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤
          A * D.scalarCurvature x ^ (3 / 2 : ℝ))
    {a : ℝ} (ha : 0 < a) (hhigh : 16 * H ≤ D.scalarCurvature (a • e2)) :
    axisWarpingRadius g a * Real.sqrt (D.scalarCurvature (a • e2)) ≤ max 8 (256 * A) := by
  let Q := D.scalarCurvature (a • e2)
  let L := Q ^ (-1 / 2 : ℝ) / (2 * A)
  have hQ : 0 < Q := hpos _
  have hL : 0 < L := div_pos (Real.rpow_pos_of_pos hQ _) (mul_pos (by norm_num) hA)
  obtain ⟨b, hab, hlength⟩ := exists_outward_radial_interval g hcomplete ha.le hL
  have hscale : 2 * L = Q ^ (-1 / 2 : ℝ) / A := by dsimp only [L]; ring
  have hfloor (u : ℝ) (hu : u ∈ Icc a b) :
      Q / 16 ≤ D.scalarCurvature (u • e2) := by
    apply (scalar_floor_on_ball_of_guarded_gradient g D hpos hreg hA hgrad hhigh _).le
    have h := radial_interval_subset_ball g hL hlength u hu
    rwa [hscale] at h
  have hbound := axisWarpingRadius_sq_le_or_mul_arclength_le D hrotation hsec
    hcomplete ha hab.le (div_pos hQ (by norm_num)) hfloor
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  rcases hbound with hsmall | hlarge
  · have hmul := (le_div_iff₀ (div_pos hQ (by norm_num : (0 : ℝ) < 16))).mp hsmall
    have hnorm : (axisWarpingRadius g a * Real.sqrt Q) ^ 2 =
        axisWarpingRadius g a ^ 2 * Q := by rw [mul_pow, hsq]
    apply le_trans _ (le_max_left _ _)
    change axisWarpingRadius g a * Real.sqrt Q ≤ 8
    nlinarith [sq_nonneg (axisWarpingRadius g a * Real.sqrt Q - 8)]
  · rw [hlength] at hlarge
    have hpow : Q ^ (-1 / 2 : ℝ) = (Real.sqrt Q)⁻¹ := by
      rw [neg_div, Real.rpow_neg hQ.le, ← Real.sqrt_eq_rpow]
    have heq : Q / 16 * axisWarpingRadius g a * L =
        (axisWarpingRadius g a * Real.sqrt Q) / (32 * A) := by
      dsimp only [L]
      rw [hpow]
      field_simp [hA.ne', hsqrt.ne']
      nlinarith [congrArg (fun q : ℝ => axisWarpingRadius g a * q) hsq]
    rw [heq] at hlarge
    have hmul := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 32) hA)).mp hlarge
    exact (show axisWarpingRadius g a * Real.sqrt Q ≤ 256 * A by linarith).trans
      (le_max_right _ _)

end PoincareConjecture.M35.Uniqueness

namespace PoincareConjecture.RepairedStandardCapExistenceData

open M35.Uniqueness



theorem exists_normalized_orbit_radius_bound (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀) :
    ∃ B H : ℝ, 0 < B ∧ 0 < H ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime,
      ∀ r : ℝ, 0 < r →
      H ≤ (E.flow.connection t).scalarCurvature (r • EuclideanSpace.single (2 : Fin 3) 1) →
      axisWarpingRadius (E.flow.metric t) r *
        Real.sqrt ((E.flow.connection t).scalarCurvature
          (r • EuclideanSpace.single (2 : Fin 3) 1)) ≤ B := by
  obtain ⟨A, H, hA, hH, hbounds⟩ :=
    M35.OrdinaryRealization.exists_unit_time_scalar_estimates P E
  refine ⟨max 8 (256 * A), 16 * H, (by positivity), mul_pos (by norm_num) hH, ?_⟩
  intro t ht r hr hhigh
  exact axisWarpingRadius_mul_sqrt_scalar_le (E.flow.connection t)
    (E.rotation_invariant t ht) (E.nonnegative_sectional t ht) (E.complete t ht)
    (E.scalar_pos ht) (Proofs.M09.scalarCurvature_contMDiff P.curvature (E.flow.connection t))
    hA (fun z hz => (hbounds t ht z hz).1) hr hhigh

end PoincareConjecture.RepairedStandardCapExistenceData
