import PoincareConjecture.Proofs.M34.Standard.CanonicalConnectionDifferenceRate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap

theorem exists_uniform_canonicalDomain_connectionRate_bound
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
      letI := hNE
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (g0 : RiemannianMetric n U) (D0 : LeviCivitaData g0)
        (g1 : RiemannianMetric n U) (D1 : LeviCivitaData g1) (p : U) (x : V n), x ∈ U →
        let B0 := g0.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        let B1 := g1.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 x‖ ≤ M) →
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 x‖ ≤ M) →
        (∀ v, a * ‖v‖ ^ 2 ≤ B0 x v v) →
        (∀ v, a * ‖v‖ ^ 2 ≤ B1 x v v) →
        ∀ (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n) (ε : ℝ), 0 < ε →
          (∑ alpha : Fin dA, 2 * qA A alpha *
            qA (canonicalDomain_connectionDifferenceRate U hU qS
              g0 D0 g1 D1 p x d H A S) alpha) ≤
            ε * (∑ beta, d beta ^ 2) + (C / ε + C) *
              ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_connectionJetRate_bound qH qA qS ha M
  refine ⟨C, hC, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g0 D0 g1 D1 p x hx B0 B1 hj0 hj1 he0 he1 d H A S ε hε
  let J0 := spatialJet 3 (fun z : ℝ × V n => B0 z.2) (0, x)
  let J1 := spatialJet 3 (fun z : ℝ × V n => B1 z.2) (0, x)
  have hM : 0 ≤ M := (norm_nonneg (iteratedFDeriv ℝ 0 B0 x)).trans (hj0 0 (by omega))
  have hJ0 : ‖J0‖ ≤ M := by
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro j
    exact hj0 j (by omega)
  have hJ1 : ‖J1‖ ≤ M := by
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro j
    exact hj1 j (by omega)
  have hh := hbound J0 J1 hJ0 hJ1 he0 he1 d H A S ε hε
  dsimp only [J0, J1, B0, B1] at hh
  rw [canonicalDomain_connectionDifferenceRate_from_jets U hU qS
    g0 D0 g1 D1 p x hx] at hh
  exact hh

end PoincareConjecture.M34
