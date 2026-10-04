import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.CanonicalCoreCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Coordinates.PartialFlowSpatialJetBounds

/-!
# Compact core bounds for the actual canonical flow

The ambient identity is an initial local isometry. The existing uniform
ellipticity and spatial-jet estimates apply to it and transfer through
the global core coefficient identity. This is Morgan-Tian Section 12.5,
pp. 309-319 and core-overlap-and-energy-majorants.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Metric jets take values in nested Hom spaces.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34

open DifferenceEnergy

/-- The actual canonical core flow has uniform ellipticity and every
finite collection of spatial jets on a fixed compact set and curvature
horizon (Section 12.5, pp. 309-319). -/
theorem partialFlow_corePullback_bounds (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0)
    {S B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI :=
      (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.isManifold_singleton
        (I := 𝓡 3) (n := ∞)
    ∃ a M : ℝ, 0 < a ∧ 1 ≤ M ∧ ∀ t ∈ Ico 0 S,
      ∀ (p : (univ : Set StandardCapSpace)) (x : StandardCapSpace), x ∈ K →
        (∀ j ≤ m, ‖iteratedFDeriv ℝ j
          (((canonicalCoreFlow F.flow).metric t).pullbackCoefficients
            (extChartAt (𝓡 3) p).symm) x‖ ≤ M) ∧
        (∀ v : StandardCapSpace, a * ‖v‖ ^ 2 ≤
          ((canonicalCoreFlow F.flow).metric t).pullbackCoefficients
            (extChartAt (𝓡 3) p).symm x v v) := by
  let :=
    (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let :=
    (isOpen_univ : IsOpen (univ : Set (V 3))).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
  obtain ⟨a, b, ha, _hb, hell⟩ :=
    partialFlow_compactPullback_ellipticity P F hSF hB.le hfull hK
  obtain ⟨M, hM, hjets⟩ :=
    partialFlow_compactPullback_spatialJet_bounds P E0 F hS hSF hB hfull hK m
  have hid (x : StandardCapSpace) (u v : TangentSpace (𝓡 3) x) :
      g0.metric.inner x u v = g0.metric.inner (id x)
        (mfderiv (𝓡 3) (𝓡 3) id x u) (mfderiv (𝓡 3) (𝓡 3) id x v) := by
    rw [mfderiv_id]
    rfl
  refine ⟨a, M, ha, hM, ?_⟩
  intro t ht p x hx
  rw [canonicalCoreFlow_chart_coefficients]
  constructor
  · intro j hj
    apply hjets j hj (U := univ) isOpen_univ contMDiff_id.contMDiffOn
      _ (fun y _ => hid y) t ht x hx (mem_univ _)
    intro y _
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ StandardCapSpace, rfl⟩
  · exact fun v => (hell t ht x hx id (hid x) v).1

end PoincareMT.M34
