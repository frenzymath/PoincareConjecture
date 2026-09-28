import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceFlux











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap




theorem exists_uniform_canonicalDomain_differenceFlux_bounds
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ CF CW : ℝ, 0 ≤ CF ∧ 0 ≤ CW ∧
      ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
        letI := hNE
        letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
        letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
        ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g)
          (g' : RiemannianMetric n U) (D' : LeviCivitaData g') (p : U) (x : V n), x ∈ U →
          let B0 := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          let B1 := g'.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 x‖ ≤ M) →
          (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 x‖ ≤ M) →
          (∀ v, a * ‖v‖ ^ 2 ≤ B0 x v v) →
          (∀ v, a * ‖v‖ ^ 2 ≤ B1 x v v) →
          (∀ (H : FH n) (A : FA n) (S : FS n),
            (∑ alpha : Fin dS, ∑ i : Fin n, curvatureContraction qS
              (canonicalDomain_curvatureDifferenceFlux U hU g D g' D' p x H A S i) alpha ^ 2) ≤
              CF * ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2))) ∧
          (∀ (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n) (ε : ℝ), 0 < ε →
            (∑ alpha : Fin dS, 2 * qS S alpha *
              canonicalDomain_curvatureDifferenceRemainder U hU qS g D g' D' p x d H A S alpha) ≤
              ε * (∑ beta, d beta ^ 2) + (CW / ε + CW) *
                ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2))) := by
  obtain ⟨CF, CW, hCF, hCW, hbound⟩ := exists_uniform_differenceJetFlux_bounds qH qA qS ha M
  refine ⟨CF, CW, hCF, hCW, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D g' D' p x hx B0 B1 hj0 hj1 he0 he1
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
  have hb := hbound J0 J1 hJ0 hJ1 he0 he1
  constructor
  · intro H A S
    have hh := hb.1 H A S
    dsimp only [J0, J1, B0, B1] at hh
    rw [canonicalDomain_curvatureDifferenceFlux_from_jets U hU g D g' D' p x hx] at hh
    exact hh
  · intro d H A S ε hε
    have hh := hb.2 d H A S ε hε
    dsimp only [J0, J1, B0, B1] at hh
    rw [canonicalDomain_curvatureDifferenceRemainder_from_jets U hU qS g D g' D' p x hx] at hh
    exact hh

end PoincareConjecture.M34
