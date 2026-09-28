import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.OperatorRicci










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]




theorem intrinsicOpenMetric_nonnegativeCurvatureOperator_iff
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (D : LeviCivitaData g) (DU : LeviCivitaData (intrinsicOpenMetric g U))
    (x : U) :
    DU.NonnegativeCurvatureOperator x ↔ D.NonnegativeCurvatureOperator (x : M) := by
  exact DU.nonnegativeCurvatureOperator_iff_of_local_isometry D
    (f := (Subtype.val : U → M)) isOpen_univ
    (contMDiff_subtype_val (I := 𝓡 3) (U := U)).contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ x)




theorem intrinsicOpenMetric_nonnegativeSectionalCurvature_of_operator
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (D : LeviCivitaData g) (DU : LeviCivitaData (intrinsicOpenMetric g U))
    (hD : ∀ x : U, D.NonnegativeCurvatureOperator (x : M)) :
    DU.NonnegativeSectionalCurvature := by
  intro x v w
  exact DU.sectional_nonneg_of_nonnegative_operator_m28 x
    ((intrinsicOpenMetric_nonnegativeCurvatureOperator_iff g U D DU x).mpr (hD x)) v w

end PoincareConjecture.M28
