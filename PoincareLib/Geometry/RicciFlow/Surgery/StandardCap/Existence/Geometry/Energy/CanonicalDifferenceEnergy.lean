import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.CanonicalDensityIntegral
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.CanonicalDifferenceEnergyRegularity

/-!
# Actual compact-cutoff canonical difference energies

The named energy is the integral of the actual nonnegative density.
On included times it agrees with the finite scalar energies. Their
closed-time continuity and interior derivatives transfer through that
identity, with eventual equality used for derivatives. This is
Morgan-Tian Section 12.5, pp. 309-319 and actual-density-integrals.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The actual curvature fiber contains three nested Hom spaces.
set_option maxSynthPendingDepth 8

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

variable {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
  (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))

/-- The compact-cutoff integral of the actual canonical density
(Section 12.5, pp. 309-319). -/
noncomputable def canonicalDifferenceEnergy (φ : V n → ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ}, RicciFlow n U J → RicciFlow n U J' → U → ℝ → ℝ :=
  letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  letI : MeasurableSpace (V n) := borel _
  letI : BorelSpace (V n) := ⟨rfl⟩
  fun F F' p t => ∫ x, φ x ^ 2 * canonicalDifferenceDensity U hU qH qA qS F F' p t x

/-- The totalized energy is nonnegative at every total time
(Section 12.5, pp. 309-319). -/
theorem canonicalDifferenceEnergy_nonneg (φ : V n → ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U) (t : ℝ),
      0 ≤ canonicalDifferenceEnergy U hU qH qA qS φ F F' p t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' p t
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _)
    (canonicalDifferenceDensity_nonneg U hU qH qA qS F F' p t x))

variable {φ : V n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
  (hφU : tsupport φ ⊆ U)

include hφ hφc hφU

/-- The actual integral energy is continuous on compact included time
sets, including the initial endpoint (Section 12.5, pp. 309-319). -/
theorem canonicalDifferenceEnergy_continuousOn :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U)
      {K : Set ℝ}, IsCompact K → K ⊆ J ∩ J' →
      ContinuousOn (canonicalDifferenceEnergy U hU qH qA qS φ F F' p) K := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' p K hK hKJ
  have hc := canonicalDomain_continuousOn_difference_energy U hU qH qA qS hφ hφc hφU
    F F' (fun t x => curvatureTrilinearMap (F.connection t) x)
    (fun t x => curvatureTrilinearMap (F'.connection t) x)
    (fun t x u v w => curvatureTrilinearMap_apply (F.connection t) x u v w)
    (fun t x u v w => curvatureTrilinearMap_apply (F'.connection t) x u v w) p K hK hKJ
  apply hc.congr
  intro t ht
  exact canonicalDifferenceDensity_integral_eq U hU qH qA qS hφ hφc hφU F F' p (hKJ ht)

/-- The actual integral energy is differentiable at every interior common
time, using an identity on a neighborhood of that time
(Section 12.5, pp. 309-319). -/
theorem canonicalDifferenceEnergy_differentiableAt :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U)
      {t : ℝ}, t ∈ interior (J ∩ J') →
      DifferentiableAt ℝ (canonicalDifferenceEnergy U hU qH qA qS φ F F' p) t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' p t ht
  have hd := canonicalDomain_hasDerivAt_difference_energy U hU qH qA qS hφ hφc hφU
    F F' (fun s x => curvatureTrilinearMap (F.connection s) x)
    (fun s x => curvatureTrilinearMap (F'.connection s) x)
    (fun s x u v w => curvatureTrilinearMap_apply (F.connection s) x u v w)
    (fun s x u v w => curvatureTrilinearMap_apply (F'.connection s) x u v w) p t ht
  apply hd.differentiableAt.congr_of_eventuallyEq
  filter_upwards [mem_interior_iff_mem_nhds.mp ht] with s hs
  exact canonicalDifferenceDensity_integral_eq U hU qH qA qS hφ hφc hφU F F' p hs

end PoincareMT.M34
