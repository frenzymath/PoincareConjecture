import PoincareConjecture.Proofs.M59.Mathlib.IntegralTopSupport
import PoincareConjecture.Proofs.M02.Topology.IntegralThreeManifoldTop
import PoincareConjecture.Proofs.M02.HurewiczInjectivity

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) X] [SimplyConnectedSpace X]

theorem integralNoncompactSimplyConnectedThreeHomology_isZero
    (x0 : X) (hnoncompact : ¬IsCompact (univ : Set X)) :
    IsZero (integralHomology X 3) := by
  classical
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace Real (Fin 3)) X
  obtain ⟨omega, hgen, hlocal⟩ := exists_integralThreeLocallyRepresentedGenerators x0
  choose basis hbasis using hgen
  have hzero (a : integralHomology X 3) : a = 0 := by
    obtain ⟨x, hx⟩ := exists_integralHomology_point_restriction_zero hnoncompact 3 a
    let A : integralSupportHomology (univ : Set X) 3 :=
      integralToRelativeHomology (univ : Set X)ᶜ 3 a
    have hrestriction (y : X) :
        integralSupportHomologyRestriction (subset_univ ({y} : Set X)) 3 A =
          integralToRelativeHomology ({y}ᶜ : Set X) 3 a :=
      integralToRelativeHomology_restriction _ 3 a
    have hconstant := integralSupportHomology_coefficient_locallyConstant 3
      omega basis hbasis hlocal A
    apply integralHomology_eq_zero_of_point_restrictions 3
      (fun K hK => (integralThreeManifoldCompactSupport K hK).1 0)
      (fun K hK => (integralThreeManifoldCompactSupport K hK).2) a
    intro y
    have he := hconstant.apply_eq_of_preconnectedSpace y x
    rw [hrestriction y, hrestriction x, hx, map_zero] at he
    apply (basis y).symm.injective
    rw [map_zero]
    exact he
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩

theorem noncompactSimplyConnectedThree_piThree_subsingleton
    (x : X) (hnoncompact : ¬IsCompact (univ : Set X))
    (hpiTwo : Subsingleton (HomotopyGroup.Pi 2 X x)) :
    Subsingleton (HomotopyGroup.Pi 3 X x) := by
  have hzero := integralNoncompactSimplyConnectedThreeHomology_isZero x hnoncompact
  have hlow (k : Nat) (hk : 1 ≤ k) (hk' : k ≤ 2) :
      Subsingleton (HomotopyGroup.Pi k X x) := by
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl
    · exact HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
    · exact hpiTwo
  constructor
  intro a b
  apply M02.homotopyGroupSingularHomologyMap_injective (TopCat.of X) x 1 hlow
  exact hzero.eq_of_tgt _ _

end PoincareConjecture.Proofs.M59
