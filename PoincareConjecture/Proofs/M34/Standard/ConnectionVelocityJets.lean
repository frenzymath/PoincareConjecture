import PoincareConjecture.Proofs.M34.Standard.CanonicalRicciGradient











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap



noncomputable def ricciGradientThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) (i j k : Fin n) : ℝ :=
  ∑ l : Fin n, covariantCurvatureThreeJet n J i l l j k




noncomputable def connectionVelocityThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) (i j : Fin n) : V n :=
  inverseMetricThreeJet n J (∑ k : Fin n,
    (-ricciGradientThreeJet n J i j k - ricciGradientThreeJet n J j k i +
      ricciGradientThreeJet n J k i j) • EuclideanSpace.proj k)



theorem continuousOn_ricciGradientThreeJet (n : ℕ) :
    ContinuousOn (ricciGradientThreeJet n) (curvatureJetDomain n 1) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro k
  apply continuousOn_finsetSum
  intro l _
  exact continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp
    (continuousOn_pi.mp (continuousOn_pi.mp
      (continuousOn_covariantCurvatureThreeJet n) i) l) l) j) k



theorem continuousOn_connectionVelocityThreeJet (n : ℕ) :
    ContinuousOn (connectionVelocityThreeJet n) (curvatureJetDomain n 1) := by
  have hC (i j k : Fin n) := continuousOn_pi.mp (continuousOn_pi.mp
    (continuousOn_pi.mp (continuousOn_ricciGradientThreeJet n) i) j) k
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  apply (contDiffOn_inverseMetricThreeJet n).continuousOn.clm_apply
  apply continuousOn_finsetSum
  intro k _
  exact (((hC i j k).neg.sub (hC j k i)).add (hC k i j)).smul continuousOn_const

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]



noncomputable def canonicalDomain_connectionVelocity :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (_D : LeviCivitaData g) (_p : U) (_x : V n)
      (_i _j : Fin n), V n := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x i j
  let C := fun i j k => ∑ l : Fin n,
    canonicalDomain_covariantCurvatureArray U hU g D p x i l l j k
  exact (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse
    (∑ k : Fin n, (-C i j k - C j k i + C k i j) • EuclideanSpace.proj k)



theorem canonicalDomain_connectionVelocity_from_jets :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
      connectionVelocityThreeJet n (spatialJet 3 (fun z : ℝ × V n =>
        g.pullbackCoefficients (extChartAt (𝓡 n) p).symm z.2) (0, x)) =
          canonicalDomain_connectionVelocity U hU g D p x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx
  funext i j
  dsimp only [connectionVelocityThreeJet, ricciGradientThreeJet,
    canonicalDomain_connectionVelocity]
  rw [canonicalDomain_inverseMetricThreeJet U hU,
    canonicalDomain_covariantCurvatureThreeJet U hU g D p x hx]

end PoincareConjecture.M34
