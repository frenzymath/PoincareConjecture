import PoincareConjecture.Proofs.M34.Standard.CanonicalCurvatureNorms
import PoincareConjecture.Proofs.M34.Standard.CurvatureReactionEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem exists_uniform_canonicalDomain_curvatureReaction_bound
    {n dH dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
      letI := hNE
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g)
        (g' : RiemannianMetric n U) (D' : LeviCivitaData g') (p : U) (x : V n), x ∈ U →
        let B0 := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        let B1 := g'.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 x‖ ≤ H) →
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 x‖ ≤ H) →
        (∀ v, a * ‖v‖ ^ 2 ≤ B0 x v v) →
        (∀ v, a * ‖v‖ ^ 2 ≤ B1 x v v) →
        ∀ R R' : FS n,
          raw R = canonicalDomain_curvatureArray U hU g D p x →
          raw R' = canonicalDomain_curvatureArray U hU g' D' p x →
          (∑ alpha : Fin dS, 2 * qS (R - R') alpha *
            curvatureContraction qS
              (modelCurvatureReactionDifference (B0 x) (B1 x) R R') alpha) ≤
            C * ((∑ i, qH (B0 x - B1 x) i ^ 2) + (∑ i, qS (R - R') i ^ 2)) := by
  obtain ⟨M, hM, hbound⟩ := canonicalDomain_background_operatorNorm_bound n ha H
  obtain ⟨C, hC, hreact⟩ := exists_uniform_modelCurvatureReaction_energy_bound qH qS
    (zero_le_one.trans hM)
  refine ⟨C, hC, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D g' D' p x hx B0 B1 hj0 hj1 he0 he1 R R' hR hR'
  have hb0 := hbound U hU hNE g D p x hx hj0 he0 R hR
  have hb1 := hbound U hU hNE g' D' p x hx hj1 he1 R' hR'
  have hxt : x ∈ (extChartAt (𝓡 n) p).target := by
    rw [canonicalOpen_extChart_target (𝕜 := ℝ) hU p]
    exact hx
  exact hreact (B0 x) (B1 x) (g.isInvertible_chartCoefficients p hxt)
    (g'.isInvertible_chartCoefficients p hxt) R R' hb0.1 hb1.1 hb0.2 hb1.2

end PoincareConjecture.M34
