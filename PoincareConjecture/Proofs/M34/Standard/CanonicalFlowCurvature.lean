import PoincareConjecture.Proofs.M03.FamilyBundleCoordinates
import PoincareConjecture.Proofs.M03.CurvatureHom
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceJetFluxParameters











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open DifferenceEnergy Proofs.M03

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]



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

end PoincareConjecture.M34
