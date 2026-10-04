import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.HomotheticLaplacian
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.NullReaction
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl

/-!
# Flatness of a terminal homothetic ancient slice

The radial tensor Laplacian and the ancient terminal null-plane inequality
force Ricci curvature to be nonpositive. Nonnegative curvature operator
then forces the full tensor to vanish. This closes the differential
obstruction in Kleiner--Lott, Theorem 41.2, Case 1, equation (41.9),
corrected 2013 journal version, printed p. 2676.

Producing the smooth radial field from a cone limit remains a geometric
obligation; this theorem does not construct that limit.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.RicciFlow

/-- A nonzero constant homothety on the terminal slice of an ancient
nonnegatively curved flow forces its full curvature norm to vanish. -/
theorem curvatureTensorNorm_eq_zero_of_terminal_homothetic_field
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureCalculus.{u}) (F : RicciFlow n M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hVsmooth : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    {c : ℝ} (hc : c ≠ 0)
    (hV : ∀ x, ∀ v : TangentSpace (𝓡 n) x,
      (F.connection 0).connection V x v = c • v) :
    ∀ x, (F.connection 0).curvatureTensorNorm x = 0 := by
  intro x
  have hD := hC.tensor_calculus n M (F.metric 0) (F.connection 0)
  have hnull := (F.connection 0).curvature_eq_zero_of_constant_covariantDerivative
    hD V hVsmooth c hV x
  have hRic (w : TangentSpace (𝓡 n) x) : (F.connection 0).ricci x w w ≤ 0 := by
    have h := F.tensorLaplacian_nonpos_on_terminal_curvature_null_vector
      hC hoperator x (V x) w hnull
    rw [(F.connection 0).tensorLaplacian_riemannEvaluation_homothetic_pair
      hD V hVsmooth c hV] at h
    exact nonpos_of_mul_nonpos_right h (mul_pos (by norm_num) (sq_pos_of_ne_zero hc))
  have hscalar : (F.connection 0).scalarCurvature x = 0 := by
    apply le_antisymm
    · exact Finset.sum_nonpos fun i _ => hRic ((F.metric 0).orthonormalBasis x i)
    · exact ((F.connection 0).curvatureOperatorBound_scalarCurvature
        hD x (hoperator 0 le_rfl x)).1
  apply le_antisymm
  · simpa only [hscalar, mul_zero] using
      (F.connection 0).curvatureTensorNorm_le_scalarCurvature hD x (hoperator 0 le_rfl x)
  · exact Real.sqrt_nonneg _

end PoincareMT.RicciFlow
