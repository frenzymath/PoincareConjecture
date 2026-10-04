import PoincareLib.Geometry.Riemannian.Surface.TotalCurvature
import PoincareLib.Geometry.Riemannian.Heat.Energy.VolumeSupport
import PoincareLib.Geometry.Curvature.Operator.SectionalBounds

/-!
# Positive total scalar curvature on the retained compact surface

Morgan--Tian Claim 11.34 and its following finite-product discussion,
printed pp. 288-289. One retained triangulation computes the same positive
scalar-curvature integral for every metric on the actual surface.

The common-triangulation argument rederives
`LeviCivitaData.integral_scalarCurvature_eq_of_compact_surface` from Horizon
`Soliton/ThreeDimensional/Noncompact/Rigidity/Levels/TotalCurvature`, retaining
the integer count as well. The exact APIs are
`exists_finite_smooth_triangulation_with_retained_coordinates`,
`integral_scalarCurvature_eq_four_pi_euler_of_length_lt_one`,
`integral_scalarCurvature_le_eight_pi`, and
`RiemannianMetric.volumeMeasure_isOpenPosMeasure`.
Reviewed derivation: `claim11_34-finite-surface-positivity.md`, section 2.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.M32

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [CompactSpace M] [ConnectedSpace M]

/-- Nonnegative curvature with a positive scalar seed gives one positive
integer cell count, equal to one or two, computing every metric's scalar
integral on the same surface. Source: Claim 11.34, pp. 288-289, and the
retained Gauss--Bonnet formula. No surface model identification is asserted. -/
theorem compact_surface_total_scalar_euler_alternative
    (g : RiemannianMetric 2 M) (D : LeviCivitaData g)
    (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (p : M) (hp : 0 < D.scalarCurvature p) :
    ∃ chi : ℤ, (chi = 1 ∨ chi = 2) ∧
      ∀ (h : RiemannianMetric 2 M) (Dh : LeviCivitaData h),
        (∫ x, Dh.scalarCurvature x ∂h.volumeMeasure) =
          4 * Real.pi * (chi : ℝ) := by
  classical
  have hnonneg (x : M) : 0 ≤ D.scalarCurvature x := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator x (hoperator x) _ _
  have hpositive : 0 < ∫ x, D.scalarCurvature x ∂g.volumeMeasure :=
    integral_pos_of_integrable_nonneg_nonzero D.continuous_scalarCurvature
      D.integrable_scalarCurvature hnonneg hp.ne'
  obtain ⟨T⟩ := Topology.Surface.exists_finite_smooth_triangulation_with_retained_coordinates
    (M := M)
  let chi : ℤ :=
    (Nat.card (Topology.Surface.Euler.CoordinateVertex
      T.refinement.coordinates T.refinement.basis) : ℤ) -
      Nat.card (Topology.Surface.FaceBoundaryEdge T.refinement.face) +
        Nat.card T.refinement.Child
  have hformula (h : RiemannianMetric 2 M) (Dh : LeviCivitaData h) :
      (∫ x, Dh.scalarCurvature x ∂h.volumeMeasure) = 4 * Real.pi * (chi : ℝ) := by
    simpa only [chi, Int.cast_add, Int.cast_sub, Int.cast_natCast] using
      T.integral_scalarCurvature_eq_four_pi_euler_of_length_lt_one Dh T.length_lt_one
  have hfour : 0 < 4 * Real.pi := by positivity
  rw [hformula g D] at hpositive
  have hchiPos : 0 < (chi : ℝ) := (mul_pos_iff_of_pos_left hfour).mp hpositive
  have hbound := D.integral_scalarCurvature_le_eight_pi
  rw [hformula g D] at hbound
  have hchiLe : (chi : ℝ) ≤ 2 := by
    apply (mul_le_mul_iff_right₀ hfour).mp
    nlinarith [hbound]
  have hchiPosInt : (0 : ℤ) < chi := by exact_mod_cast hchiPos
  have hchiLeInt : chi ≤ 2 := by exact_mod_cast hchiLe
  exact ⟨chi, by omega, hformula⟩

end PoincareMT.M32
