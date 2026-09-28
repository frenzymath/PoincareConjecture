import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarFourJet
import PoincareConjecture.Proofs.M45.Ch9_Models.LocalScalar
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_CylinderCoefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M45

open SpacetimeBounds M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance scalarReadoutCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance scalarReadoutCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace
noncomputable local instance scalarReadoutTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup
noncomputable local instance scalarReadoutTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace
noncomputable local instance scalarReadoutFirstNorm :
    NormedAddCommGroup (E →L[ℝ] MetricTwoJet 3) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance scalarReadoutFirstSpace :
    NormedSpace ℝ (E →L[ℝ] MetricTwoJet 3) := ContinuousLinearMap.toNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem metricTwoJet_eventuallyEq {A B : E → MetricCoefficient 3} {x : E}
    (h : A =ᶠ[𝓝 x] B) : metricTwoJet A =ᶠ[𝓝 x] metricTwoJet B := by
  filter_upwards [h, h.fderiv (𝕜 := ℝ), (h.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)]
    with y h0 h1 h2
  simp only [metricTwoJet, h0, h1, h2]



theorem scalarMetricFourJet_congr {A B : E → MetricCoefficient 3} {x : E}
    (h : A =ᶠ[𝓝 x] B) : scalarMetricFourJet A x = scalarMetricFourJet B x := by
  have hJ := metricTwoJet_eventuallyEq h
  simp only [scalarMetricFourJet, hJ.self_of_nhds, hJ.fderiv_eq,
    (hJ.fderiv (𝕜 := ℝ)).fderiv_eq]





theorem jetScalarLaplacian_pullbackCoefficients
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {x : E} (hx : x ∈ U) :
    jetScalarLaplacian (scalarMetricFourJet (g.pullbackCoefficients f) x) =
      D.laplacian D.scalarCurvature (f x) := by
  obtain ⟨gE, DE, V, hV, hxV, hVU, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hU hx (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt)
      (fun y _ a b => g.symm (f y) _ _)
      (fun y hy a ha => by
        apply g.pos (f y)
        intro hz
        apply ha
        apply (hinv y hy).injective
        rw [map_zero]
        exact hz)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients f :=
    eventually_of_mem (hV.mem_nhds hxV) hmetric
  rw [← scalarMetricFourJet_congr heq, jetScalarLaplacian_scalarMetricFourJet DE]
  have hm (y : E) (hy : y ∈ V) (a b : TangentSpace (𝓡 3) y) :
      gE.inner y a b = g.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b) :=
    congrArg (fun B => B a b) (hmetric y hy)
  have hs : DE.scalarCurvature =ᶠ[𝓝 x] D.scalarCurvature ∘ f := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact DE.scalarCurvature_eq_of_local_isometry D hV (hf.mono hVU) hm hy
  rw [DE.laplacian_eq_of_eventuallyEq hs]
  exact DE.laplacian_comp_of_metric_pullback D (hf.contMDiffAt (hU.mem_nhds hx))
    (eventually_of_mem (hV.mem_nhds hxV) (fun y hy => hinv y (hVU hy)))
    (eventually_of_mem (hV.mem_nhds hxV) hm) (model_scalar_smooth D (f x))

end PoincareConjecture.M45
