import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Evolution of Hamilton's singular-time correction

The Ricci term `Ric / (2 * (t - T₀))` in Hamilton's two-tensor has a
time derivative supplied by the Ricci evolution equation and the quotient
rule. This is one term of the tensor evolution, not matrix positivity.

See Chow et al., Part II, equation (15.9), PDF p. 288, and the tensor
evolution calculation in Section 15.2.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The singular-time Ricci correction has its geometric evolution value on
fixed tangent inputs, including within-domain derivatives at endpoints. -/
lemma ricci_timeCorrection_hasDerivWithinAt
    (hC : RicciFlowCurvatureTheory.{u}) (J : Set ℝ) (F : RicciFlow n M J)
    (T₀ t : ℝ) (ht : t ∈ J) (hT : t ≠ T₀)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).ricci x u v / (2 * (s - T₀)))
      (((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![u, v] +
        (F.connection t).ricciReaction x u v) / (2 * (t - T₀)) -
        (F.connection t).ricci x u v / (2 * (t - T₀) ^ 2)) J t := by
  have hden : HasDerivWithinAt (fun s : ℝ ↦ 2 * (s - T₀)) 2 J t := by
    simpa using (((hasDerivAt_id t).sub_const T₀).const_mul 2).hasDerivWithinAt
  have hne : t - T₀ ≠ 0 := sub_ne_zero.mpr hT
  apply ((hC.ricci_evolution n M J F t ht x u v).fun_div hden
    (mul_ne_zero (by norm_num) hne)).congr_deriv
  field_simp [hne]

/-- At an interior time, the same formula gives the ordinary derivative. -/
lemma ricci_timeCorrection_hasDerivAt
    (hC : RicciFlowCurvatureTheory.{u}) (J : Set ℝ) (F : RicciFlow n M J)
    (T₀ t : ℝ) (ht : t ∈ interior J) (hT : t ≠ T₀)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ (F.connection s).ricci x u v / (2 * (s - T₀)))
      (((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![u, v] +
        (F.connection t).ricciReaction x u v) / (2 * (t - T₀)) -
        (F.connection t).ricci x u v / (2 * (t - T₀) ^ 2)) t := by
  exact (ricci_timeCorrection_hasDerivWithinAt hC J F T₀ t
    (interior_subset ht) hT x u v).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)

end Poincare.RicciFlow.Harnack
