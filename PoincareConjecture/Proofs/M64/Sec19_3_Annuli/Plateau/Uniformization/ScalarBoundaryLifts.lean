import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus












set_option autoImplicit false

noncomputable section

open Set

namespace PoincareConjecture




def scalarIdentityDegreeOneLift : M64PeriodicDegreeOneLift where
  map := id
  monotone := monotone_id
  period_shift := by intro x; dsimp
  lipschitz_constant := 1
  lipschitz_nonnegative := by norm_num
  lipschitz_on := by intro x y; simp




theorem scalarIdentityDegreeOneLift_apply (x : ℝ) :
    scalarIdentityDegreeOneLift.map x = x := rfl




theorem scalarIdentityDegreeOneLift_period :
    ∀ x : ℝ, scalarIdentityDegreeOneLift.map (x + curvePeriod) =
      scalarIdentityDegreeOneLift.map x + curvePeriod :=
  scalarIdentityDegreeOneLift.period_shift




theorem exists_scalar_boundary_degree_one_lifts :
    ∃ (sigma0 sigma1 : M64PeriodicDegreeOneLift),
      sigma0.map = id ∧ sigma1.map = id := by
  exact ⟨scalarIdentityDegreeOneLift, scalarIdentityDegreeOneLift,
    rfl, rfl⟩

end PoincareConjecture
