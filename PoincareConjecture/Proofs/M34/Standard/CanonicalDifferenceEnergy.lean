import PoincareConjecture.Proofs.M34.Standard.CanonicalDensityIntegral
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergyRegularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

variable {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
  (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))



noncomputable def canonicalDifferenceEnergy (φ : V n → ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ}, RicciFlow n U J → RicciFlow n U J' → U → ℝ → ℝ :=
  letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  letI : MeasurableSpace (V n) := borel _
  letI : BorelSpace (V n) := ⟨rfl⟩
  fun F F' p t => ∫ x, φ x ^ 2 * canonicalDifferenceDensity U hU qH qA qS F F' p t x



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

end PoincareConjecture.M34
