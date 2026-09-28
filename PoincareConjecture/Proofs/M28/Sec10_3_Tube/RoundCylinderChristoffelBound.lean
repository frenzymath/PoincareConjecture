import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.ModelChristoffel

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

namespace PoincareConjecture.M28.tube

open PoincareConjecture.Proofs.M28.NeckAnalysis

theorem exists_bound_roundCylinderChristoffel_fderiv :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : ℝ), u < 1 → ∀ (q : UnitTwoSphere) (s : ℝ),
        ∀ a b d : Fin 3,
          ‖fderiv ℝ (fun p : RoundCylinderCoordinates =>
            roundCylinderChristoffel u
              (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_roundCylinderChristoffel_jets 1
  refine ⟨C, hC, ?_⟩
  intro u hu q s a b d
  have h := hbound u hu q s 1 (by omega) a b d
  simpa only [norm_iteratedFDeriv_one] using h

end PoincareConjecture.M28.tube
