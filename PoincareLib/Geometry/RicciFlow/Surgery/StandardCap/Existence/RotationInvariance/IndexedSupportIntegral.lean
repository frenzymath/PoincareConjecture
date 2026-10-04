import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.IndexedEnergy
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.BoundarySupportIntegral
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.EndNeighborIntegral

/-!
# Support integrals for the actual indexed energies

The two exceptional rows use the fixed core band. Every later row uses
the three actual neighboring translated energies. This is Morgan-Tian
Section 12.5, pp. 309-319 and core-energy-comparison-api.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Actual curvature takes values in three nested Hom spaces.
set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT.M34

open DifferenceEnergy

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
  {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))

/-- The unweighted actual density integral on each cutoff support
(Section 12.5, pp. 309-319). -/
noncomputable def capDifferenceSupportIntegral {J J' : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
    (p : endReferenceRegion e) : ℕ → ℝ → ℝ :=
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  letI : MeasurableSpace StandardCapSpace := borel _
  letI : BorelSpace StandardCapSpace := ⟨rfl⟩
  fun i t => match i with
  | 0 => ∫ x in tsupport (coreEnergyCutoff e),
      actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t) x
  | j + 1 => ∫ x in tsupport (endEnergyCutoff e),
      canonicalDifferenceDensity (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
        (endPullbackFlow e F j (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
        (endPullbackFlow e F' j (by have := Nat.cast_nonneg (α := ℝ) j; linarith)) p t x

/-- Each actual support integral is nonnegative at every total time
(Section 12.5, pp. 309-319). -/
theorem capDifferenceSupportIntegral_nonneg {J J' : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
    (p : endReferenceRegion e) (i : ℕ) (t : ℝ) :
    0 ≤ capDifferenceSupportIntegral e qH qA qS F F' p i t := by
  cases i with
  | zero => exact integral_nonneg (actualDifferenceEnergyDensity_nonneg qH qA qS _ _)
  | succ j => exact integral_nonneg (canonicalDifferenceDensity_nonneg _ _ qH qA qS _ _ p t)

/-- One geometric constant controls both boundary rows and all interior
rows of the actual support integrals (Section 12.5, pp. 309-319). -/
theorem exists_capDifferenceSupportIntegral_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
      (p : endReferenceRegion e) {t : ℝ}, t ∈ J ∩ J' →
      let E := capDifferenceEnergy e qH qA qS F F' p
      let S := capDifferenceSupportIntegral e qH qA qS F F' p
      S 0 t ≤ C * (E 0 t + E 1 t + E 2 t) ∧
      S 1 t ≤ C * (E 0 t + E 1 t + E 2 t) ∧
      ∀ j : ℕ, S (j + 2) t ≤ C * (E (j + 1) t + E (j + 2) t + E (j + 3) t) := by
  let := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  obtain ⟨Cb, hCb, hb⟩ := exists_boundarySupport_integral_bound e qH qA qS
  obtain ⟨Cn, _hCn, hn⟩ := exists_endNeighbor_integral_bound e qH qA qS
  refine ⟨max Cb Cn, hCb.trans (le_max_left _ _), ?_⟩
  intro J J' F F' p t ht E S
  have hE (i) : 0 ≤ E i t := capDifferenceEnergy_nonneg e qH qA qS F F' p i t
  have hboundary : S 0 t ≤ Cb * (E 0 t + E 1 t + E 2 t) ∧
      S 1 t ≤ Cb * (E 0 t + E 1 t + E 2 t) := by
    simpa only [S, E, capDifferenceSupportIntegral, capDifferenceEnergy,
      canonicalDifferenceEnergy, canonicalCoreFlow_chart_density] using hb F F' p ht
  have hnbr (j : ℕ) : S (j + 2) t ≤ Cn * (E (j + 1) t + E (j + 2) t + E (j + 3) t) := by
    simpa only [S, E, capDifferenceSupportIntegral, capDifferenceEnergy,
      canonicalDifferenceEnergy] using hn F F' p ht j
  have hB : 0 ≤ E 0 t + E 1 t + E 2 t := add_nonneg (add_nonneg (hE 0) (hE 1)) (hE 2)
  exact ⟨hboundary.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB),
    hboundary.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB),
    fun j => (hnbr j).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg (add_nonneg (hE (j + 1)) (hE (j + 2))) (hE (j + 3))))⟩

end PoincareMT.M34
