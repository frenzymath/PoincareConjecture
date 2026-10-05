import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Neck.Spatial
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control

/-!
# Uniform scalar comparison on strong necks

Morgan--Tian Claims 11.32-11.33, printed pp. 287-288, use scalar comparison
on the actual spatial necks. Appendix A.2/A.11, pp. 497-498/503-504, supplies
the uniform small-accuracy estimates through the eligible curvature library.

The elementary scale identity is re-derived from the read-only donor
`M34/Thm12_28_12_29_Lifetime/CapPersistenceBoundaryScalar.lean`,
`EpsilonNeck.scale_sq_mul_scalar_center`. The later module is not imported.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

/-- Scalar normalization of the prescribed spatial neck scale, as in
Definition 9.78, printed p. 232. Positivity excludes inverse junk values. -/
theorem neckScale_sq_mul_scalar_center
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) :
    N.scale ^ 2 * N.connection.scalarCurvature N.center = 1 := by
  rw [N.scale_eq_scalar, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg N.scalar_center_pos.le, ← Real.sqrt_eq_rpow, inv_pow,
    Real.sq_sqrt N.scalar_center_pos.le, inv_mul_cancel₀ N.scalar_center_pos.ne']

/-- The coordinate scalar estimate covers the entire spatial neck carrier,
with one threshold before all manifolds and necks (Appendix A.11, p. 503). -/
theorem exists_neck_scalarControl {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
        ∀ N : EpsilonNeck g, N.epsilon ≤ epsilon₀ → ∀ x ∈ N.carrier,
          |N.scale ^ 2 * N.connection.scalarCurvature x - 1| < alpha := by
  obtain ⟨epsilon₀, hpos, hsmall, hcontrol⟩ :=
    EpsilonNeck.exists_ambient_curvature_control.{u} halpha
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N he x hx
  have hmap : N.coordinate_map (N.coordinate_inverse x) = x := by
    rw [← N.coordinate_map_eq
      ((N.coordinate_inverse x).1, ⟨(N.coordinate_inverse x).2,
        (N.coordinate_inverse_mem x hx).2⟩)]
    exact congrArg Subtype.val (N.coordinate_inverse_right x hx)
  have h := (hcontrol N N.connection he (N.coordinate_inverse x).1
    (N.coordinate_inverse_mem x hx).2).1
  simpa only [hmap] using h

/-- One universal threshold gives the strict factor-two scalar comparison
on every strong neck, as used in Claims 11.32-11.33, pp. 287-288. -/
theorem exists_strongNeck_scalarComparison :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
        ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ epsilon₀ →
          ∀ x ∈ N.carrier,
            (F.connection t).scalarCurvature N.center / 2 <
                (F.connection t).scalarCurvature x ∧
              (F.connection t).scalarCurvature x <
                2 * (F.connection t).scalarCurvature N.center := by
  obtain ⟨epsilon₀, hpos, hsmall, hcontrol⟩ :=
    exists_neck_scalarControl.{u} (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro F t epsilon N he x hx
  have hhalf : epsilon < 1 / 2 := he.trans_lt (hsmall.trans_lt (by norm_num))
  have hbound := hcontrol (spatialNeck N hhalf) he x hx
  have hnorm := neckScale_sq_mul_scalar_center (spatialNeck N hhalf)
  change |N.scale ^ 2 * (F.connection t).scalarCurvature x - 1| < 1 / 2 at hbound
  change N.scale ^ 2 * (F.connection t).scalarCurvature N.center = 1 at hnorm
  have hscale : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
  constructor
  · apply (mul_lt_mul_iff_right₀ hscale).mp
    nlinarith [(abs_lt.mp hbound).1]
  · apply (mul_lt_mul_iff_right₀ hscale).mp
    nlinarith [(abs_lt.mp hbound).2]

end PoincareMT.M32
