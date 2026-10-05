import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.SliceGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.ScalarLowerBound.ScalarPositivity
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.SliceGeometry.PinchingIsometry

/-!
# The nonnegative branch of the actual generalized flow

Morgan-Tian, Theorem 12.28, pp. 323-324, through the nonnegative branch
of Theorem 11.1. The actual least-sectional definition has zero negative
defect, and the unit slice homothety preserves it.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT

/-- Chapter 4's negative defect vanishes when all actual sectional numerators are nonnegative.
Used in Theorem 12.28, pp. 323-324. -/
theorem LeviCivitaData.negativeCurvaturePart_eq_zero_of_nonnegative
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M)
    (h : ∀ u v : TangentSpace (𝓡 3) x, 0 ≤ D.curvatureTensor x u v u v) :
    D.negativeCurvaturePart x = 0 := by
  apply max_eq_right
  apply neg_nonpos.mpr
  apply Real.sInf_nonneg
  rintro k ⟨u, v, _, rfl⟩
  exact h u v

namespace M35.OrdinaryRealization

/-- The retained-slice identification preserves the exact least-sectional negative defect.
Used in Theorem 12.28, pp. 323-324. -/
theorem negativeCurvaturePart_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) :
    (connection F t).negativeCurvaturePart ((sliceDiffeomorph ht).symm x) =
      (F.connection t).negativeCurvaturePart x :=
  Proofs.M13.negativeCurvaturePart_eq_one (slice_calculus P F ht)
    (slice_homothety F ht) (F.connection t) (connection F t) x

/-- Theorem 12.28's actual generalized realization satisfies M30's nonnegative branch
(pp. 323-324). -/
theorem generalized_nonnegative (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) :
    generalizedNonnegativeCurvature (generalizedFlow E.flow.base.flow) := by
  have hscalar (t : ℝ) (ht : t ∈ Ico 0 E.flow.base.lifetime)
      (x : (slice (Ico 0 E.flow.base.lifetime) t).carrier) :
      0 ≤ (generalizedFlow E.flow.base.flow).scalar ⟨t, x⟩ :=
    ((E.scalar_pos ht x.val).trans_eq (scalar_eq P E.flow.base.flow ht x.val).symm).le
  have hneg (t : ℝ) (ht : t ∈ Ico 0 E.flow.base.lifetime)
      (x : (slice (Ico 0 E.flow.base.lifetime) t).carrier) :
      (connection E.flow.base.flow t).negativeCurvaturePart x = 0 :=
    (negativeCurvaturePart_eq P E.flow.base.flow ht x.val).trans
      ((E.flow.connection t).negativeCurvaturePart_eq_zero_of_nonnegative x.val
        (E.nonnegative_sectional t ht x.val))
  refine ⟨(fun t ht x => ⟨hscalar t ht x, hneg t ht x⟩), ?_⟩
  intro t ht x
  refine ⟨(by linarith [hscalar t ht x]), ?_⟩
  intro hpos
  exact (not_lt_of_ge (hneg t ht x).le hpos).elim

end M35.OrdinaryRealization

end PoincareMT
