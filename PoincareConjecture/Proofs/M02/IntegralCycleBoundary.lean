import PoincareConjecture.Proofs.M02.IntegralChains
import PoincareConjecture.Proofs.M02.Topology.IntegralSubdivision
import Mathlib.Algebra.Homology.Refinements
import Mathlib.Algebra.Category.ModuleCat.EpiMono

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace PoincareConjecture.Proofs.M02

open PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X]

theorem integral_cycle_boundary_of_zero_homology_class
    (n : Nat)
    (a : integralCoefficient ⟶ (integralChains X).X (n + 1))
    (ha : a ≫ (integralChains X).d (n + 1) n = 0)
    (hz : (integralChains X).liftCycles a n (by simp) ha ≫
      (integralChains X).homologyπ (n + 1) = 0) :
    ∃ b : integralCoefficient ⟶ (integralChains X).X (n + 2),
      b ≫ (integralChains X).d (n + 2) (n + 1) = a := by
  obtain ⟨A', π, hπ, x₁, hfac⟩ :=
    (HomologicalComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
      (K := integralChains X) (n + 2) (n + 1) n (by simp) (by simp) a ha).mp hz
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective π).mp hπ (ULift.up 1)
  let s : integralCoefficient ⟶ A' :=
    (integralCoefficientHomEquiv A').symm z
  have hs : s ≫ π = 𝟙 _ := by
    apply (integralCoefficientHomEquiv integralCoefficient).injective
    change (s ≫ π) (ULift.up 1) = (𝟙 _ : integralCoefficient ⟶ integralCoefficient)
      (ULift.up 1)
    change π (s (ULift.up 1)) = (ULift.up 1 : ULift.{u} ℤ)
    have hs_eval : s (ULift.up 1) = z := by
      simpa [s] using integralCoefficientHomEquiv_symm_apply A' z (ULift.up 1)
    rw [hs_eval, hz]
  refine ⟨s ≫ x₁, ?_⟩
  calc
    (s ≫ x₁) ≫ (integralChains X).d (n + 2) (n + 1) =
        s ≫ (x₁ ≫ (integralChains X).d (n + 2) (n + 1)) := Category.assoc _ _ _
    _ = s ≫ (π ≫ a) := by rw [← hfac]
    _ = (s ≫ π) ≫ a := (Category.assoc _ _ _).symm
    _ = a := by rw [hs, Category.id_comp]

end

end PoincareConjecture.Proofs.M02
