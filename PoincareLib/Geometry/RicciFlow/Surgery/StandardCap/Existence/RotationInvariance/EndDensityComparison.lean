import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.CompatibleEndDensity

/-!
# Uniform actual difference density on end overlaps

The actual metric, connection and curvature transition identities combine
with compact bounds on the three fixed derivatives. One constant precedes
both flows, all translations, times and points. This is the pointwise
overlap step in Morgan-Tian Section 12.5, pp. 309-319 and
coordinate-density-and-slabs.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The actual density contains three nested curvature Hom fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareMT.M34

open DifferenceEnergy

/-- The actual density in a translated chart is uniformly controlled by
the actual neighboring-chart density on compact overlaps
(Section 12.5, pp. 309-319). -/
theorem exists_endTransition_density_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {K : Set StandardCapSpace} (hK : IsCompact K) (hKU : K ⊆ endReferenceRegion e) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
      (p : endReferenceRegion e) (r : ℝ), (r = -1 ∨ r = 0 ∨ r = 1) →
      ∀ (s : ℝ) (hs : -3 < s) (hrs : -3 < r + s) (t : ℝ) (x : endReferenceRegion e),
        (x : StandardCapSpace) ∈ K → endAxialTranslation e r x ∈ K →
        actualDifferenceEnergyDensity qH qA qS
          ((endPullbackFlow e F (r + s) hrs).connection t)
          ((endPullbackFlow e F' (r + s) hrs).connection t) x ≤
            C * actualDifferenceEnergyDensity qH qA qS
              ((endPullbackFlow e F s hs).connection t)
              ((endPullbackFlow e F' s hs).connection t) (endReferenceTransition e p r x) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  obtain ⟨C, hC, hcompare⟩ := exists_compatibleEnd_density_bound e qH qA qS hK hKU
  refine ⟨C, hC, ?_⟩
  intro J J' F F' p r hr s hs hrs t x hx hshift
  have hrpos : -3 < r := by rcases hr with rfl | rfl | rfl <;> norm_num
  exact hcompare _ _ _ _
    ((endPullbackFlow e F (r + s) hrs).connection t)
    ((endPullbackFlow e F' (r + s) hrs).connection t)
    ((endPullbackFlow e F s hs).connection t) ((endPullbackFlow e F' s hs).connection t)
    p r hr (endReferenceTransition_metric e F p r hrpos s hs hrs t)
      (endReferenceTransition_metric e F' p r hrpos s hs hrs t) x hx hshift

end PoincareMT.M34
