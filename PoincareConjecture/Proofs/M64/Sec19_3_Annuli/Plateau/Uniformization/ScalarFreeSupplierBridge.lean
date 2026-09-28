import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryLifts
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction














set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]





theorem m64FreeConformalModulusApproximation_of_fixed
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (hfixed : M64ConformalModulusApproximation g c0 c1) :
    M64FreeConformalModulusApproximation g c0 c1 := by
  intro A ε hε
  obtain ⟨r, hr, A', hAint, henergy⟩ := hfixed A ε hε
  refine ⟨r, hr, scalarIdentityDegreeOneLift, scalarIdentityDegreeOneLift,
    A', ?_, ?_⟩
  · simpa only [scalarIdentityDegreeOneLift] using hAint
  · simpa only [scalarIdentityDegreeOneLift] using henergy

end PoincareConjecture
