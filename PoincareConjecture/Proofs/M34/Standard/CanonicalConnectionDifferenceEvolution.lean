import PoincareConjecture.Proofs.M34.Standard.CanonicalConnectionTensorRate
import PoincareConjecture.Proofs.M34.Standard.UniformCanonicalConnectionRate











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

variable {n dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]




theorem canonicalDomain_hasDerivAt_connection_difference_factored
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') {t : ℝ},
      t ∈ interior J → t ∈ interior J' → ∀ (p x : U) (R0 R1 : V n → FS n),
        (∀ y ∈ U, raw (R0 y) =
          canonicalDomain_curvatureArray U hU (F.metric t) (F.connection t) p y) →
        (∀ y ∈ U, raw (R1 y) =
          canonicalDomain_curvatureArray U hU (F'.metric t) (F'.connection t) p y) →
        DifferentiableAt ℝ R0 (x : V n) → DifferentiableAt ℝ R1 (x : V n) →
        HasDerivAt (F := FA n)
          (fun s => CovariantDerivative.difference
            (F.connection s).connection (F'.connection s).connection x)
          (canonicalDomain_connectionDifferenceRate U hU qS
            (F.metric t) (F.connection t) (F'.metric t) (F'.connection t) p (x : V n)
            (fun beta => fderiv ℝ (fun y => qS (R0 y - R1 y) beta.1) (x : V n)
              (EuclideanSpace.single beta.2 1))
            ((F.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm (x : V n) -
              (F'.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm (x : V n))
            (CovariantDerivative.difference
              (F.connection t).connection (F'.connection t).connection x)
            (R0 (x : V n) - R1 (x : V n))) t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' t ht ht' p x R0 R1 hR0 hR1 hd0 hd1
  have hf := canonicalDomain_connectionVelocity_difference U hU qS
    (F.metric t) (F.connection t) (F'.metric t) (F'.connection t)
    p (x : V n) x.property R0 R1 hR0 hR1 hd0 hd1
  have hpoint : (extChartAt (𝓡 n) p).symm (x : V n) = x :=
    canonicalOpen_chart_symm_apply hU p x
  rw [hpoint] at hf
  rw [← hf]
  exact canonicalDomain_hasDerivAt_connection_difference_tensor U hU F F' ht ht' p x




theorem canonicalDomain_deriv_connection_difference_coordinate
    {dA : ℕ} (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') {t : ℝ},
      t ∈ interior J → t ∈ interior J' → ∀ (p x : U) (R0 R1 : V n → FS n),
        (∀ y ∈ U, raw (R0 y) =
          canonicalDomain_curvatureArray U hU (F.metric t) (F.connection t) p y) →
        (∀ y ∈ U, raw (R1 y) =
          canonicalDomain_curvatureArray U hU (F'.metric t) (F'.connection t) p y) →
        DifferentiableAt ℝ R0 (x : V n) → DifferentiableAt ℝ R1 (x : V n) →
        ∀ alpha : Fin dA,
          deriv (fun s => qA (CovariantDerivative.difference
            (F.connection s).connection (F'.connection s).connection x) alpha) t =
          qA (canonicalDomain_connectionDifferenceRate U hU qS
            (F.metric t) (F.connection t) (F'.metric t) (F'.connection t) p (x : V n)
            (fun beta => fderiv ℝ (fun y => qS (R0 y - R1 y) beta.1) (x : V n)
              (EuclideanSpace.single beta.2 1))
            ((F.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm (x : V n) -
              (F'.metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm (x : V n))
            (CovariantDerivative.difference
              (F.connection t).connection (F'.connection t).connection x)
            (R0 (x : V n) - R1 (x : V n))) alpha := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' t ht ht' p x R0 R1 hR0 hR1 hd0 hd1 alpha
  let L : FA n →L[ℝ] ℝ := (EuclideanSpace.proj alpha).comp qA.toContinuousLinearMap
  exact (L.hasFDerivAt.comp_hasDerivAt t
    (canonicalDomain_hasDerivAt_connection_difference_factored U hU qS
      F F' ht ht' p x R0 R1 hR0 hR1 hd0 hd1)).deriv

end PoincareConjecture.M34
