import PoincareConjecture.Proofs.M35.Thm12_28.ScalarOperatorScaling
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_local_scalar_operator_realization
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (f : E → M)
    {U : Set E} (hU : IsOpen U) {p : E} (hp : p ∈ U)
    (hf : ∀ z ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f z)
    (hi : ∀ z ∈ U, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible)
    (hR : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature (f p)) :
    ∃ (g' : RiemannianMetric 3 E) (D' : LeviCivitaData g'),
      (∀ᶠ z in 𝓝 p, g'.euclideanCoefficients z = g.pullbackCoefficients f z) ∧
      D'.scalarCurvature p = D.scalarCurvature (f p) ∧
      scalarGradientNorm g' D' p = scalarGradientNorm g D (f p) ∧
      D'.laplacian D'.scalarCurvature p + 2 * D'.ricciNormSq p =
        D.laplacian D.scalarCurvature (f p) + 2 * D.ricciNormSq (f p) := by
  obtain ⟨g', D', V, hVo, hpV, hVU, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization hU hp (g.pullbackCoefficients f)
      (fun z hz => (g.contDiffAt_pullbackCoefficients (hf z hz)).contDiffWithinAt)
      (fun z _ v w => g.symm (f z) _ _)
      (fun z hz v hv => by
        apply g.pos (f z)
        intro heq
        apply hv
        apply (hi z hz).injective
        exact heq.trans (map_zero (mfderiv (𝓡 3) (𝓡 3) f z)).symm)
  have hmetric (z : E) (hz : z ∈ V) : ∀ u v : E,
      g'.inner z u v = g.inner (f z)
        (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v) := by
    intro u v
    exact congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A u v) (hcoeff z hz)
  have hscalar : D'.scalarCurvature =ᶠ[𝓝 p] D.scalarCurvature ∘ f := by
    filter_upwards [hVo.mem_nhds hpV] with z hz
    exact scalarCurvature_eq_pullback_euclidean D' D (hf z (hVU hz))
      (Filter.mem_of_superset (hU.mem_nhds (hVU hz)) fun y hy => hi y hy)
      (Filter.mem_of_superset (hVo.mem_nhds hz) fun y hy => hmetric y hy)
  have hinv : ∀ᶠ z in 𝓝 p, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible :=
    Filter.mem_of_superset (hU.mem_nhds hp) fun z hz => hi z hz
  have hmet : ∀ᶠ z in 𝓝 p, ∀ u v : E, g'.inner z u v = g.inner (f z)
      (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v) :=
    Filter.mem_of_superset (hVo.mem_nhds hpV) fun z hz => hmetric z hz
  exact ⟨g', D', Filter.mem_of_superset (hVo.mem_nhds hpV) (fun z hz => hcoeff z hz),
    hscalar.self_of_nhds,
    scalarGradientNorm_eq_pullback_of_scalar_germ D' D (hf p hp) (hi p hp)
      (hmetric p hpV) hR hscalar,
    scalar_evolution_eq_pullback_of_scalar_germ D' D (hf p hp) hinv hmet hR hscalar⟩

theorem exists_scaled_scalar_operator_realization
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q)
    (f : E → E) {U : Set E} (hU : IsOpen U) {p : E} (hp : p ∈ U)
    (hf : ∀ z ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f z)
    (hi : ∀ z ∈ U, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible) :
    ∃ (g' : RiemannianMetric 3 E) (D' : LeviCivitaData g'),
      (∀ᶠ z in 𝓝 p, g'.euclideanCoefficients z = Q • g.pullbackCoefficients f z) ∧
      D'.scalarCurvature p = D.scalarCurvature (f p) / Q ∧
      scalarGradientNorm g' D' p = scalarGradientNorm g D (f p) / (Q * Real.sqrt Q) ∧
      D'.laplacian D'.scalarCurvature p + 2 * D'.ricciNormSq p =
        (D.laplacian D.scalarCurvature (f p) + 2 * D.ricciNormSq (f p)) / Q ^ 2 := by
  let G : RiemannianMetric 3 E := M13.scaleSmoothMetric g Q hQ
  let DG := M13.scaleLeviCivitaData D Q hQ
  obtain ⟨g', D', hcoeff, hscalar, hgrad, hevol⟩ :=
    exists_local_scalar_operator_realization G DG f hU hp hf hi
      (scalarCurvature_contDiffAt_euclidean DG (f p)).contMDiffAt
  have hsc : DG.scalarCurvature (f p) = D.scalarCurvature (f p) / Q :=
    M13.homothety_scalarCurvature_eq g G (Diffeomorph.refl (𝓡 3) E ∞) Q hQ
      (M13.identity_metricHomothety g Q hQ) D DG (f p)
  exact ⟨g', D', hcoeff, hscalar.trans hsc,
    hgrad.trans (scale_scalarGradientNorm D Q hQ (f p)),
    hevol.trans (scale_scalar_evolution D Q hQ (f p))⟩

end PoincareConjecture.M35
