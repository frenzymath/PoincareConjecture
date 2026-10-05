import PoincareLib.Geometry.Riemannian.Connection.OpenDomain

/-!
# Levi-Civita data for canonical open domains

The singleton chart structure of a nonempty open subset of Euclidean space
equals its inherited `Opens` chart structure. Transport along this equality
provides the existing open-domain Levi-Civita construction with the exact
singleton chart structure used by canonical coordinate metrics.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareMT

/-- The singleton inclusion chart agrees with the inherited open-domain atlas,
including the chosen total chart maps. -/
theorem canonicalDomain_chartedSpace_eq_opens
    {E : Type*} [TopologicalSpace E] (U : Set E) (hU : IsOpen U) [Nonempty U] :
    hU.isOpenEmbedding_subtypeVal.singletonChartedSpace =
      @Opens.instChartedSpace E E _ _ (chartedSpaceSelf E) ⟨U, hU⟩ := by
  let e := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  apply ChartedSpace.ext
  · change {e} = ⋃ _ : U, {e.trans (OpenPartialHomeomorph.refl E)}
    simp only [OpenPartialHomeomorph.trans_refl, iUnion_const]
  · funext x
    change e = e.trans (OpenPartialHomeomorph.refl E)
    exact e.trans_refl.symm

/-- Construct a compatible torsion-free smooth connection while retaining the
canonical singleton chart structure of the metric. -/
noncomputable def RiemannianMetric.canonicalMetricLeviCivitaData
    {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U] :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ g : RiemannianMetric n U, LeviCivitaData g := by
  have htransport : ∀ C : ChartedSpace (EuclideanSpace ℝ (Fin n)) U,
      C = @Opens.instChartedSpace _ _ _ _
        (chartedSpaceSelf (EuclideanSpace ℝ (Fin n))) ⟨U, hU⟩ →
      letI := C
      ∀ hM : IsManifold (𝓡 n) ∞ U,
      letI := hM
      ∀ g : RiemannianMetric n U, LeviCivitaData g := by
    intro C hC
    subst C
    intro hM g
    exact g.openEuclideanLeviCivitaData (⟨U, hU⟩ : Opens (EuclideanSpace ℝ (Fin n)))
  exact htransport _ (canonicalDomain_chartedSpace_eq_opens U hU) _

end PoincareMT
