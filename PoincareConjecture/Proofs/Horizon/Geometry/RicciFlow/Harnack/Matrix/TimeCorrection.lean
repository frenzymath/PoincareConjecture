import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring












set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



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
