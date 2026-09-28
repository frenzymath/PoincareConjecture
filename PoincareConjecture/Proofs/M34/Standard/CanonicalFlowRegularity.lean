import PoincareConjecture.Proofs.M03.ConnectionDifference
import PoincareConjecture.Proofs.M34.Standard.CanonicalFlowCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open DifferenceEnergy Proofs.M03

variable {n : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]

theorem canonicalDomain_inner_eq_pullbackCoefficients :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g : RiemannianMetric n U) (p : U) (x : V n), x ∈ U →
      g.inner ((extChartAt (𝓡 n) p).symm x) =
        g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g p x hx
  have hr : (extChartAt (𝓡 n) p).symm x = (⟨x, hx⟩ : U) :=
    canonicalOpen_chart_symm_apply hU p ⟨x, hx⟩
  rw [hr]
  exact (RiemannianMetric.pullbackCoefficients_canonicalChart U hU g p ⟨x, hx⟩).symm

set_option maxHeartbeats 800000 in

theorem canonicalDomain_contDiffOn_flow_metric
    {dH : ℕ} (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J : Set ℝ} (F : RicciFlow n U J) (p : U), ContDiffOn (F := FH n) ℝ ∞
      (fun z : ℝ × V n => ((F.metric z.1).inner
        ((extChartAt (𝓡 n) p).symm z.2) : FH n))
      (J ×ˢ U) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J F p
  let BH := fun x : U => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ
  have hbase : (chartAt (V n) p).source ⊆ (trivializationAt (FH n) BH p).baseSet := by
    simp [BH, hom_trivializationAt_baseSet]
  have hc := contDiffOn_family_bundle_coordinates (E := BH) qH
    (fun t x => (F.metric t).inner x) F.smooth p hbase
  have hf : ContDiffOn ℝ ∞
      (fun z : ℝ × V n => qH ((F.metric z.1).inner ((extChartAt (𝓡 n) p).symm z.2)))
      (J ×ˢ U) := by
    simpa only [BH, constantChart_bilinear_coordinates (𝓡 n)
      (canonicalOpen_chart_eq hU), canonicalOpen_chart_target hU, extChartAt_coe_symm,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq] using hc
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    qH.symm.contDiff.comp_contDiffOn hf

set_option maxHeartbeats 800000 in

theorem canonicalDomain_contDiffOn_connection_difference
    {dA : ℕ} (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U),
      ContDiffOn (F := FA n) ℝ ∞ (fun z : ℝ × V n => (CovariantDerivative.difference
        (F.connection z.1).connection (F'.connection z.1).connection
        ((extChartAt (𝓡 n) p).symm z.2) : FA n)) ((J ∩ J') ×ˢ U) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' p
  let BA := fun x : U => TangentSpace (𝓡 n) x →L[ℝ]
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x
  let A : ℝ → U → FA n := fun s x => CovariantDerivative.difference
    (F.connection s).connection (F'.connection s).connection x
  have hF := F.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J from inter_subset_left) subset_rfl)
  have hF' := F'.smooth.mono (Set.prod_mono
    (show J ∩ J' ⊆ J' from inter_subset_right) subset_rfl)
  have hsm := contMDiffOn_connection_family_difference hF hF' F.connection F'.connection
  have hbase : (chartAt (V n) p).source ⊆ (trivializationAt (FA n) BA p).baseSet := by
    simp only [BA, hom_trivializationAt_baseSet,
      constantChart_tangent_baseSet (𝓡 n) (canonicalOpen_chart_eq hU), inter_self]
    exact subset_univ _
  have hc := contDiffOn_family_bundle_coordinates (E := BA) qA A hsm p hbase
  have hf : ContDiffOn ℝ ∞
      (fun z : ℝ × V n => qA (A z.1 ((extChartAt (𝓡 n) p).symm z.2))) ((J ∩ J') ×ˢ U) := by
    simpa only [BA, constantChart_vectorBilinear_coordinates (𝓡 n)
      (canonicalOpen_chart_eq hU), canonicalOpen_chart_target hU, extChartAt_coe_symm,
      modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq] using hc
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    qA.symm.contDiff.comp_contDiffOn hf

end PoincareConjecture.M34
