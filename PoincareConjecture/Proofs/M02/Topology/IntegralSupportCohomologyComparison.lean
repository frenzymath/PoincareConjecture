import PoincareConjecture.Proofs.M02.Topology.IntegralCohomologyExcision
import PoincareConjecture.Proofs.M02.Topology.IntegralMayerVietorisSplit

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSumQuotient_projective (A B : Set X) (n : Nat) :
    CategoryTheory.Projective ((integralSumQuotient A B).X n) := by
  let := integralChains_projective X n
  let r : CategoryTheory.Retract ((integralSumQuotient A B).X n)
      ((integralChains X).X n) :=
    { i := ModuleCat.ofHom (integralSumQuotientSection A B n)
      r := (integralSumAmbientProjection A B).f n
      retract := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        exact integralSumQuotientSection_rightInverse A B n }
  exact r.projective

theorem integralSumComparison_dual_quasiIso
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (integralDualMap (integralSumComparison A B)) := by
  let : ∀ n, CategoryTheory.Projective ((integralSumQuotient A B).X n) :=
    integralSumQuotient_projective A B
  let : ∀ n, CategoryTheory.Projective ((integralRelativeChains (A ∪ B)).X n) :=
    integralRelativeChains_projective (A ∪ B)
  exact integralDualMap_quasiIso_of_projective _ (integralSumComparison_quasiIso A B hA hB)

theorem integralSumComparison_cohomology_isIso
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : Nat) :
    IsIso (homologyMap (integralDualMap (integralSumComparison A B)) n) := by
  let := integralSumComparison_dual_quasiIso A B hA hB
  infer_instance

end PoincareConjecture.Proofs.M02.Topology
