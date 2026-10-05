import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CanonicalRicciGradient

/-!
# The native connection-velocity readout on metric three-jets

Tracing the actual covariant curvature derivative gives the covariant
Ricci derivative. The inverse metric raises its three-term cyclic
combination. This continuous jet readout will be identified with the
actual connection time derivative, as in Morgan-Tian Section 12.5,
pp. 309-319 and canonical-native-connection-rate.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The jet space and inverse bilinear map have nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareMT.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap

/-- The formal covariant Ricci derivative is the output/first-input trace
of the covariant curvature derivative (Section 12.5, pp. 309-319). -/
noncomputable def ricciGradientThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) (i j k : Fin n) : ℝ :=
  ∑ l : Fin n, covariantCurvatureThreeJet n J i l l j k

/-- The three-term covariant Ricci combination, raised with the formal
inverse metric, gives the connection-velocity readout
(Section 12.5, pp. 309-319). -/
noncomputable def connectionVelocityThreeJet (n : ℕ)
    (J : Jet (V n) (MetricCoefficient n) 3) (i j : Fin n) : V n :=
  inverseMetricThreeJet n J (∑ k : Fin n,
    (-ricciGradientThreeJet n J i j k - ricciGradientThreeJet n J j k i +
      ricciGradientThreeJet n J k i j) • EuclideanSpace.proj k)

/-- The formal covariant Ricci gradient is continuous on invertible
metric three-jets (Section 12.5, pp. 309-319). -/
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

/-- The formal connection-velocity readout is continuous on the same
invertible three-jet domain (Section 12.5, pp. 309-319). -/
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

/-- The candidate native velocity formed from the actual inverse metric
and actual covariant curvature array (Section 12.5, pp. 309-319). -/
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

/-- The continuous formal velocity readout equals the actual canonical
geometric expression on the true open target (Section 12.5, pp. 309-319). -/
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

end PoincareMT.M34
