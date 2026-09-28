import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ModulusConfinementInterval

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => m64AnnulusDomain

theorem m64WeightedModulusConfinement_exists_of_approximation_and_bounds
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A0 : M64Annulus g c0 c1)
    (hconf : M64ConformalModulusApproximation g c0 c1)
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hlower : ∀ (r : ℝ), 0 < r → ∀ A : M64Annulus g c0 c1,
      IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
        r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume →
      alpha * r ≤ m64ClassicalWeightedGramEnergy g A r ∧
        beta * r⁻¹ ≤ m64ClassicalWeightedGramEnergy g A r) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
      M64WeightedModulusConfinement g c0 c1 lo hi := by
  have hleast : 0 ≤ m64LeastAnnulusArea g c0 c1 :=
    m64LeastAnnulusArea_nonneg A0
  have hlevel : 0 < m64LeastAnnulusArea g c0 c1 + 1 := by
    linarith
  let lo := beta / (m64LeastAnnulusArea g c0 c1 + 1)
  let hi := (m64LeastAnnulusArea g c0 c1 + 1) / alpha
  refine ⟨lo, hi, ?_, ?_, ?_⟩
  · dsimp [lo]
    exact div_pos hbeta hlevel
  · dsimp [lo, hi]
    exact m64WeightedModulusConfinement_interval_nonempty_of_approximation
      A0 hconf halpha hbeta hlower
  · dsimp [lo, hi]
    exact m64WeightedModulusConfinement_of_two_sided_lower_bounds
      A0 halpha hbeta hlower

end PoincareConjecture
