import PoincareConjecture.Proofs.M34.Standard.LocalPullbackRealization
import PoincareConjecture.Proofs.M34.Standard.ScalarAnalyticJet
import PoincareConjecture.Proofs.M34.Standard.ScalarGradientHomothety
import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionHomothety
import PoincareConjecture.Proofs.M47.BlowupControlsCapCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E" => StandardCapSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

noncomputable local instance capReadoutCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capReadoutCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

theorem cap_analyticJet_normalizedPullback
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ y ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y))
    {Q : ℝ} (hQ : 0 < Q) {x : E} (hx : x ∈ U) :
    M34.scalarAnalyticJet 3 (spatialJet 4
      (fun z : ℝ × E => Q • g.pullbackCoefficients f z.2) (0, x)) =
      (D.scalarCurvature (f x) / Q,
        scalarGradientNorm g D (f x) / Q ^ (3 / 2 : ℝ),
        (D.laplacian D.scalarCurvature (f x) + 2 * D.ricciNormSq (f x)) / Q ^ 2) := by
  let gQ := m01RescaledMetric g Q hQ
  obtain ⟨gE, DE, V, hV, hxV, hVU, hmetric⟩ :=
    gQ.exists_local_immersive_pullback_realization f hU hx hf hinj
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x]
      (fun y => Q • g.pullbackCoefficients f y) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact hmetric y hy
  have hjet : spatialJet 4 (fun z : ℝ × E => gE.euclideanCoefficients z.2) (0, x) =
      spatialJet 4 (fun z : ℝ × E => Q • g.pullbackCoefficients f z.2) (0, x) := by
    funext j
    exact (heq.iteratedFDeriv ℝ j).self_of_nhds
  rw [← hjet, M34.scalarAnalyticJet_spatialJet DE, ← scalarGradientNorm_eq_tangentNorm]
  have hmetricQ (y : E) (hy : y ∈ V) (v w : TangentSpace (𝓡 3) y) :
      gE.inner y v w = Q * g.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) :=
    congrArg (fun B : MetricCoefficient 3 => B v w) (hmetric y hy)
  exact Prod.ext
    (DE.scalarCurvature_eq_of_local_homothety D hQ hV (hf.mono hVU) hmetricQ hxV)
    (Prod.ext (scalarGradientNorm_eq_of_local_homothety DE D hQ hV
      (hf.mono hVU) hmetricQ hxV)
      (DE.scalarEvolutionNumerator_eq_of_local_homothety D hQ hV
        (hf.mono hVU) hmetricQ hxV))

end PoincareConjecture.M47
