import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction















set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "S" => m64AnnulusDomain



theorem m64WeightedModulusConfinement_of_two_sided_lower_bounds
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A0 : M64Annulus g c0 c1) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hlower : ∀ (r : ℝ), 0 < r → ∀ A : M64Annulus g c0 c1,
      IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
        r⁻¹ * m60AreaGram g A.map p 1 1) / 2) S volume →
      alpha * r ≤ m64ClassicalWeightedGramEnergy g A r ∧
        beta * r⁻¹ ≤ m64ClassicalWeightedGramEnergy g A r) :
    M64WeightedModulusConfinement g c0 c1
      (beta / (m64LeastAnnulusArea g c0 c1 + 1))
      ((m64LeastAnnulusArea g c0 c1 + 1) / alpha) := by
  have hleast : 0 ≤ m64LeastAnnulusArea g c0 c1 :=
    m64LeastAnnulusArea_nonneg A0
  have hlevel : 0 < m64LeastAnnulusArea g c0 c1 + 1 := by
    linarith
  intro r hr A hA hupper
  have hbounds := hlower r hr A hA
  have hright : r <
      (m64LeastAnnulusArea g c0 c1 + 1) / alpha := by
    apply (lt_div_iff₀ halpha).2
    simpa [mul_comm] using hbounds.1.trans_lt hupper
  have hleft : beta / (m64LeastAnnulusArea g c0 c1 + 1) < r := by
    apply (div_lt_iff₀ hlevel).2
    have hstrict : beta * r⁻¹ < m64LeastAnnulusArea g c0 c1 + 1 :=
      hbounds.2.trans_lt hupper
    have hmul := mul_lt_mul_of_pos_right hstrict hr
    have hinv : beta * r⁻¹ * r = beta := by
      field_simp [hr.ne']
    rw [hinv] at hmul
    simpa [mul_comm] using hmul
  exact ⟨hleft.le, hright.le⟩

end PoincareConjecture
