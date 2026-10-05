import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.ActualDifferenceDensity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CanonicalDifferenceRegularity

/-!
# The actual difference density in canonical coordinates

The total inverse chart supplies a scalar coordinate field. Its geometric
value and regularity are used only on the true open target; included-time
continuity also covers the initial endpoint. This is Morgan-Tian
Section 12.5, pp. 309-319 and actual-density-integrals.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The actual curvature fiber contains three nested Hom spaces.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

variable {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
  (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))

/-- The actual difference density composed with the canonical inverse
chart, with regularity subsequently guarded by the true target
(Section 12.5, pp. 309-319). -/
noncomputable def canonicalDifferenceDensity :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ}, RicciFlow n U J → RicciFlow n U J' → U → ℝ → V n → ℝ :=
  letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  fun F F' p t x => actualDifferenceEnergyDensity qH qA qS
    (F.connection t) (F'.connection t) ((extChartAt (𝓡 n) p).symm x)

/-- On subtype points the chart density is the actual pointwise density
(Section 12.5, pp. 309-319). -/
theorem canonicalDifferenceDensity_coe :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
      (p : U) (t : ℝ) (x : U),
      canonicalDifferenceDensity U hU qH qA qS F F' p t x =
        actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t) x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' p t x
  dsimp only [canonicalDifferenceDensity]
  rw [show (extChartAt (𝓡 n) p).symm (x : V n) = x from
    canonicalOpen_chart_symm_apply hU p x]

/-- The total chart density remains nonnegative everywhere, including
outside the true chart target (Section 12.5, pp. 309-319). -/
theorem canonicalDifferenceDensity_nonneg :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
      (p : U) (t : ℝ) (x : V n), 0 ≤ canonicalDifferenceDensity U hU qH qA qS F F' p t x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' p t x
  exact actualDifferenceEnergyDensity_nonneg qH qA qS _ _ _

/-- The actual chart density is jointly continuous on the common included
time-space domain, without an endpoint derivative assumption
(Section 12.5, pp. 309-319). -/
theorem canonicalDifferenceDensity_continuousOn :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U),
      ContinuousOn (fun z : ℝ × V n => canonicalDifferenceDensity U hU qH qA qS
        F F' p z.1 z.2) ((J ∩ J') ×ˢ U) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' p
  dsimp only [canonicalDifferenceDensity, actualDifferenceEnergyDensity]
  obtain ⟨hH, hA, hS⟩ := canonicalDomain_contDiffOn_difference_coordinates U hU qH qA qS
    F F' (fun t x => curvatureTrilinearMap (F.connection t) x)
    (fun t x => curvatureTrilinearMap (F'.connection t) x)
    (fun t x u v w => curvatureTrilinearMap_apply (F.connection t) x u v w)
    (fun t x u v w => curvatureTrilinearMap_apply (F'.connection t) x u v w) p
  have hsq {d : ℕ} (f : ℝ × V n → EuclideanSpace ℝ (Fin d))
      (hf : ContinuousOn f ((J ∩ J') ×ˢ U)) :
      ContinuousOn (fun z => ∑ i, f z i ^ 2) ((J ∩ J') ×ˢ U) :=
    continuousOn_finsetSum _ (fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn
        hf).pow 2)
  intro z hz
  exact (((hsq _ hH.continuousOn) z hz).add ((hsq _ hA.continuousOn) z hz)).add
    ((hsq _ hS.continuousOn) z hz)

/-- Each included common time has a continuous actual chart density
throughout the true target (Section 12.5, pp. 309-319). -/
theorem canonicalDifferenceDensity_continuousOn_slice :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U)
      {t : ℝ}, t ∈ J ∩ J' → ContinuousOn (canonicalDifferenceDensity U hU qH qA qS F F' p t) U := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' p t ht x hx
  exact (canonicalDifferenceDensity_continuousOn U hU qH qA qS F F' p (t, x) ⟨ht, hx⟩).comp
    (continuous_const.prodMk continuous_id).continuousWithinAt (fun _ hy => ⟨ht, hy⟩)

end PoincareMT.M34
