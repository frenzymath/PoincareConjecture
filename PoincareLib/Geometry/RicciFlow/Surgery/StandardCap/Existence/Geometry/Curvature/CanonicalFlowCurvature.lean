import PoincareLib.Geometry.RicciFlow.Local.Energy.Coordinates.FamilyBundleCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coordinates.FamilyBundleCoordinates
import PoincareLib.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureHom
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureHom
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrilinear
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricCompactBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricInverse
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.CanonicalDifferenceJetFluxParameters

/-!
# Actual smooth curvature representatives on a canonical domain

The actual trilinear curvature family from M03 has ordinary joint smooth
coordinates on the canonical open domain. Its raw entries are exactly the
arrays used by the uniform energy coefficients. This supplies actual
representatives and their regularity in Morgan-Tian Section 12.5,
pp. 309-319; see canonical-connection-difference-rate.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The curvature family has three nested Hom fibers.
set_option maxSynthPendingDepth 8

open Set Bundle
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

open DifferenceEnergy Proofs.M03

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

/-- Every actual curvature representative has the canonical raw entries
at every total time and inverse-chart value (Section 12.5, pp. 309-319). -/
theorem canonicalDomain_raw_flow_curvature :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J : Set ℝ} (F : RicciFlow n U J) (R : ℝ → U → FS n),
      (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
      ∀ (p : U) (t : ℝ) (x : V n),
        raw (R t ((extChartAt (𝓡 n) p).symm x)) =
          canonicalDomain_curvatureArray U hU (F.metric t) (F.connection t) p x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J F R hR p t x
  funext l j k m
  change EuclideanSpace.proj l (R t ((extChartAt (𝓡 n) p).symm x)
    (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)) = _
  rw [hR]
  rfl

set_option maxHeartbeats 800000 in
-- Comparing the native three-slot bundle with its fixed-model instance is costly.
/-- Any actual curvature representative is jointly smooth in the fixed
canonical coordinates on the true time-space domain, including its time
boundary (Section 12.5, pp. 309-319). -/
theorem canonicalDomain_contDiffOn_flow_curvature
    {dS : ℕ} (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J : Set ℝ} (F : RicciFlow n U J) (R : ℝ → U → FS n),
      (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
      ∀ p : U, ContDiffOn ℝ ∞
        (fun z : ℝ × V n => R z.1 ((extChartAt (𝓡 n) p).symm z.2)) (J ×ˢ U) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J F R hR p
  obtain ⟨R0, hR0, hsm⟩ := exists_contMDiffOn_curvature_family_trilinearMap F.smooth F.connection
  have heq : R0 = R := by
    funext t x
    ext u v w
    exact (hR0 t x u v w).trans (hR t x u v w).symm
  rw [heq] at hsm
  let BS := fun x : U => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  have hbase : (chartAt (V n) p).source ⊆ (trivializationAt (FS n) BS p).baseSet := by
    simp only [BS, hom_trivializationAt_baseSet,
      constantChart_tangent_baseSet (𝓡 n) (canonicalOpen_chart_eq hU), inter_self]
    exact subset_univ _
  have hcoord := contDiffOn_family_bundle_coordinates (E := BS) qS R hsm p hbase
  have hfixed : ContDiffOn ℝ ∞
      (fun z : ℝ × V n => qS (R z.1 ((extChartAt (𝓡 n) p).symm z.2))) (J ×ˢ U) := by
    simpa only [BS, constantChart_vectorTrilinear_coordinates (𝓡 n)
      (canonicalOpen_chart_eq hU), canonicalOpen_chart_target hU, extChartAt_coe_symm,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq] using hcoord
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    qS.symm.contDiff.comp_contDiffOn hfixed

end PoincareMT.M34
