import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.Model
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.NormalizedChart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRoundComponent

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {epsilon : ℝ} (N : SingularRoundComponent g epsilon)

theorem exists_normalCoordinateMetrics (p : N.model.carrier) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) N.model.carrier)
      (g₀ h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
      (_D₀ : LeviCivitaData g₀) (_Dh : LeviCivitaData h)
      (U : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen U ∧ (0 : EuclideanSpace ℝ (Fin 3)) ∈ U ∧ U ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      (∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible) ∧
      (∀ y ∈ U, g₀.euclideanCoefficients y = N.model_metric.pullbackCoefficients e y) ∧
      (∀ y ∈ U, h.euclideanCoefficients y = N.normalizedMetric.pullbackCoefficients e y) ∧
      g₀.euclideanCoefficients 0 = innerSL ℝ ∧
      CoordinateExponential.christoffelBilinear g₀.euclideanCoefficients 0 = 0 := by
  obtain ⟨e, he0, hep, he, hei, _hgauss, hzero, hΓ⟩ :=
    N.model_metric.exists_normalized_exponential_chart_firstJet p
  have hd : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have realize (k : RiemannianMetric 3 N.model.carrier) :
      ∃ (k' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (_D : LeviCivitaData k')
        (V : Set (EuclideanSpace ℝ (Fin 3))),
        IsOpen V ∧ (0 : EuclideanSpace ℝ (Fin 3)) ∈ V ∧ V ⊆ e.source ∧
          ∀ y ∈ V, k'.euclideanCoefficients y = k.pullbackCoefficients e y := by
    apply RiemannianMetric.exists_local_realization e.open_source he0
      (k.pullbackCoefficients e)
    · exact fun y hy => (k.contDiffAt_pullbackCoefficients
        (he.contMDiffAt (e.open_source.mem_nhds hy))).contDiffWithinAt
    · exact fun y _ v w => k.symm (e y) _ _
    · intro y hy v hv
      apply k.pos (e y)
      intro hz
      apply hv
      apply hd.mfderiv_injective hy
      rw [map_zero]
      convert! hz using 1
  obtain ⟨g₀, D₀, U₀, hU₀, h0U₀, hU₀e, hg₀⟩ := realize N.model_metric
  obtain ⟨h, Dh, Uh, hUh, h0Uh, hUhe, hh⟩ := realize N.normalizedMetric
  refine ⟨e, g₀, h, D₀, Dh, U₀ ∩ Uh, hU₀.inter hUh, ⟨h0U₀, h0Uh⟩,
    fun _ hy => hU₀e hy.1, hep, he, hei, ?_,
    fun y hy => hg₀ y hy.1, fun y hy => hh y hy.2,
    (hg₀ 0 h0U₀).trans hzero, ?_⟩
  · intro y hy
    exact ⟨hd.mfderiv (hU₀e hy.1), rfl⟩
  · have heq : g₀.euclideanCoefficients =ᶠ[𝓝 0] N.model_metric.pullbackCoefficients e :=
      Filter.eventually_of_mem (hU₀.mem_nhds h0U₀) hg₀
    unfold CoordinateExponential.christoffelBilinear at hΓ ⊢
    rw [heq.self_of_nhds, heq.fderiv_eq]
    exact hΓ

end PoincareConjecture.SingularRoundComponent
