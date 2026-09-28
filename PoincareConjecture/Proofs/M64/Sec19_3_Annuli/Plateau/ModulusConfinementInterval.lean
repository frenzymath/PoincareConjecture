import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ModulusConfinementFromBounds

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => m64AnnulusDomain

theorem m64WeightedModulusConfinement_interval_nonempty_of_approximation
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A0 : M64Annulus g c0 c1)
    (hconf : M64ConformalModulusApproximation g c0 c1)
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hlower : ∀ (r : ℝ), 0 < r → ∀ A : M64Annulus g c0 c1,
      IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
        r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume →
      alpha * r ≤ m64ClassicalWeightedGramEnergy g A r ∧
        beta * r⁻¹ ≤ m64ClassicalWeightedGramEnergy g A r) :
    beta / (m64LeastAnnulusArea g c0 c1 + 1) ≤
      (m64LeastAnnulusArea g c0 c1 + 1) / alpha := by
  have hleast : 0 ≤ m64LeastAnnulusArea g c0 c1 :=
    m64LeastAnnulusArea_nonneg A0
  have hlevel : 0 < m64LeastAnnulusArea g c0 c1 + 1 := by
    linarith
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨A, hA⟩ := m64LeastAnnulusArea_near_minimizer A0 hquarter
  obtain ⟨r, hr, A', hA'int, hweighted⟩ := hconf A (1 / 4) hquarter
  have hupper : m64ClassicalWeightedGramEnergy g A' r <
      m64LeastAnnulusArea g c0 c1 + 1 / 2 := by
    linarith
  have hbounds := hlower r hr A' hA'int
  have henergy : 0 ≤ m64ClassicalWeightedGramEnergy g A' r := by
    exact (mul_nonneg halpha.le hr.le).trans hbounds.1
  have hinv : 0 ≤ beta * r⁻¹ :=
    mul_nonneg hbeta.le (inv_nonneg.mpr hr.le)
  have hprod0 := mul_le_mul hbounds.1 hbounds.2 hinv henergy
  have hcancel : (alpha * r) * (beta * r⁻¹) = alpha * beta := by
    field_simp [hr.ne']
  rw [hcancel] at hprod0
  have hupper_nonneg : 0 ≤
      m64LeastAnnulusArea g c0 c1 + 1 / 2 := by
    linarith
  have hupper_sq :
      m64ClassicalWeightedGramEnergy g A' r *
          m64ClassicalWeightedGramEnergy g A' r <
        (m64LeastAnnulusArea g c0 c1 + 1 / 2) ^ 2 := by
    have hs := (sq_lt_sq₀ henergy hupper_nonneg).2 hupper
    simpa only [pow_two] using hs
  have hprod : alpha * beta <
      (m64LeastAnnulusArea g c0 c1 + 1 / 2) ^ 2 := by
    exact hprod0.trans_lt hupper_sq
  apply (div_le_div_iff₀ hlevel halpha).2
  nlinarith [hprod]

end PoincareConjecture
