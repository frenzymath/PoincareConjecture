import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CanonicalConnectionTensorRate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.UniformCanonicalConnectionRate

/-!
# The actual factored connection-difference evolution

The native fixed-model derivative equals the four-family canonical rate.
Every scalar coordinate therefore has the stated genuine time derivative,
with no equality of the two initial metrics required. This is Morgan-Tian
Section 12.5, pp. 309-319 and the owned
canonical-connection-difference-rate derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The actual connection differences use nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

variable {n dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

/-- The full actual connection-difference derivative has its exact
four-family factorization on the common time interior
(Section 12.5, pp. 309-319). -/
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

/-- The scalar time derivative of each actual connection-difference
coordinate equals the coordinate of the factored rate
(Section 12.5, pp. 309-319). -/
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

end PoincareMT.M34
