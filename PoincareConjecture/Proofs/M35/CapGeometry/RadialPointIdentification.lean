import PoincareConjecture.Proofs.M35.CapGeometry.NormalizedOrbitRadius

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M35.Uniqueness

noncomputable def standardRotationDiffeomorph
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toFun := standardRotation A
  invFun := standardRotation A⁻¹
  left_inv := by
    intro x
    simpa only [inv_inv] using standardRotation_inv_apply A⁻¹ x
  right_inv := standardRotation_inv_apply A
  contMDiff_toFun := contMDiff_iff_contDiff.mpr
    (Matrix.toEuclideanLin A.1).toContinuousLinearMap.contDiff
  contMDiff_invFun := contMDiff_iff_contDiff.mpr
    (Matrix.toEuclideanLin (A⁻¹).1).toContinuousLinearMap.contDiff

theorem rotational_scalar_edist_eq_axis (P : M35StandardCapPredecessors)
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (x : StandardCapSpace) :
    D.scalarCurvature x = D.scalarCurvature (‖x‖ • EuclideanSpace.single (2 : Fin 3) 1) ∧
      g.edist 0 x = g.edist 0 (‖x‖ • EuclideanSpace.single (2 : Fin 3) 1) := by
  obtain ⟨A, hA⟩ := exists_axis_rotation x
  let e := standardRotationDiffeomorph A
  have he : MetricHomothety g g e 1 := by
    intro y u v
    change g.inner (standardRotation A y)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y u)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y v) = _
    simpa only [one_mul] using hrotation A y u v
  have H := P.metric_homothety StandardCapSpace StandardCapSpace g g e 1 zero_lt_one he
  have hAx : e (‖x‖ • EuclideanSpace.single (2 : Fin 3) 1) = x := hA
  have hAz : e 0 = 0 := (Matrix.toEuclideanLin A.1).map_zero
  constructor
  · have hs := H.scalar_eq D D (‖x‖ • EuclideanSpace.single (2 : Fin 3) 1)
    rw [hAx, div_one] at hs
    exact hs
  · have hd := H.edist_eq 0 (‖x‖ • EuclideanSpace.single (2 : Fin 3) 1)
    rw [hAz, hAx, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hd
    exact hd

end PoincareConjecture.M35.Uniqueness

namespace PoincareConjecture.RepairedStandardCapExistenceData

open M35.Uniqueness

theorem exists_normalized_orbit_radius_bound_all_points (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀) :
    ∃ B H : ℝ, 0 < B ∧ 0 < H ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime,
      ∀ x : StandardCapSpace, x ≠ 0 → H ≤ (E.flow.connection t).scalarCurvature x →
      axisWarpingRadius (E.flow.metric t) ‖x‖ *
        Real.sqrt ((E.flow.connection t).scalarCurvature x) ≤ B := by
  obtain ⟨B, H, hB, hH, hbound⟩ := E.exists_normalized_orbit_radius_bound P
  refine ⟨B, H, hB, hH, ?_⟩
  intro t ht x hx hhigh
  have hs := (rotational_scalar_edist_eq_axis P (E.flow.connection t)
    (E.rotation_invariant t ht) x).1
  rw [hs] at hhigh ⊢
  exact hbound t ht ‖x‖ (norm_pos_iff.mpr hx) hhigh

end PoincareConjecture.RepairedStandardCapExistenceData
