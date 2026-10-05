import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.FiniteBilinearCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CanonicalConnectionVelocity

/-!
# The actual connection-difference tensor derivative

Finite continuous-linear reconstruction assembles the already proved
native basis derivatives into the full fixed-model tensor derivative.
Every fixed scalar energy coordinate then inherits its actual time
derivative. This is Morgan-Tian Section 12.5, pp. 309-319 and the owned
canonical-connection-difference-rate derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Connection differences and their coordinate maps have nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

/-- Actual basis derivatives reconstruct the full connection-difference
tensor derivative in the fixed model norm (Section 12.5, pp. 309-319). -/
theorem canonicalDomain_hasDerivAt_connection_difference_tensor :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') {t : ℝ},
      t ∈ interior J → t ∈ interior J' → ∀ p x : U,
        HasDerivAt (F := FA n)
          (fun s => CovariantDerivative.difference
            (F.connection s).connection (F'.connection s).connection x)
          (ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2)
            (fun j i => canonicalDomain_connectionVelocity U hU (F.metric t) (F.connection t)
                p (x : V n) i j -
              canonicalDomain_connectionVelocity U hU (F'.metric t) (F'.connection t)
                p (x : V n) i j)) t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' t ht ht' p x
  let L : (Fin n → Fin n → V n) →L[ℝ] FA n :=
    ContinuousLinearMap.piLpBilinearFromCoordinates
  have hd : HasDerivAt (F := Fin n → Fin n → V n)
      (fun s j i => CovariantDerivative.difference
        (F.connection s).connection (F'.connection s).connection x
          (EuclideanSpace.single j 1) (EuclideanSpace.single i 1))
      (fun j i => canonicalDomain_connectionVelocity U hU (F.metric t) (F.connection t)
          p (x : V n) i j -
        canonicalDomain_connectionVelocity U hU (F'.metric t) (F'.connection t)
          p (x : V n) i j) t := by
    apply (hasDerivAt_pi (𝕜 := ℝ) (E' := fun _ : Fin n => Fin n → V n)).mpr
    intro j
    apply (hasDerivAt_pi (𝕜 := ℝ) (E' := fun _ : Fin n => V n)).mpr
    intro i
    exact canonicalDomain_hasDerivAt_connection_difference U hU F F' ht ht' p x i j
  have hmodel := L.hasFDerivAt.comp_hasDerivAt t hd
  apply hmodel.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro s
  exact (ContinuousLinearMap.piLpBilinearFromCoordinates_evaluations
    (p := 2) (q := 2) (𝕜 := ℝ) (I := Fin n) (J := Fin n) (F := V n)
    (CovariantDerivative.difference (F.connection s).connection
      (F'.connection s).connection x : FA n)).symm

/-- A fixed scalar energy coordinate has the corresponding coordinate of
the genuine reconstructed connection-difference derivative
(Section 12.5, pp. 309-319). -/
theorem canonicalDomain_hasDerivAt_connection_difference_coordinate
    {dA : ℕ} (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') {t : ℝ},
      t ∈ interior J → t ∈ interior J' → ∀ (p x : U) (alpha : Fin dA),
        HasDerivAt
          (fun s => qA (CovariantDerivative.difference
            (F.connection s).connection (F'.connection s).connection x) alpha)
          (qA (ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2)
            (fun j i => canonicalDomain_connectionVelocity U hU (F.metric t) (F.connection t)
                p (x : V n) i j -
              canonicalDomain_connectionVelocity U hU (F'.metric t) (F'.connection t)
                p (x : V n) i j)) alpha) t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' t ht ht' p x alpha
  let L : FA n →L[ℝ] ℝ := (EuclideanSpace.proj alpha).comp qA.toContinuousLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt t
    (canonicalDomain_hasDerivAt_connection_difference_tensor U hU F F' ht ht' p x)

end PoincareMT.M34
