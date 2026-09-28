import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.InteriorRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.MinimizingPath








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem exists_spatial_minimizing_backwardPath (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ α : BackwardTimePath K.flow 0 0 τ,
      α.curve 0 = p ∧
      backwardLLength K.flow 0 0 τ α.curve =
        2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ ∧
      ∀ β : BackwardTimePath K.flow 0 0 τ, β.curve 0 = p →
        backwardLLength K.flow 0 0 τ α.curve ≤ backwardLLength K.flow 0 0 τ β.curve := by
  let : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 2)
  obtain ⟨paths, γ, _, hanti, haction, hγ, hγ0, hlim, _⟩ :=
    K.exists_spatial_minimizing_uniform_limit p hτ
  have hreg := K.minimizing_uniform_limit_contMDiffOn p hτ paths hanti haction γ hγ hγ0 hlim
  obtain ⟨m, t, x, Q, _, ht, hta, htb, hQ, _⟩ :=
    exists_compact_partition_of_uniform_limit
      (fun x : M => (chartAt (EuclideanSpace ℝ (Fin 2)) x).source)
      (fun x => (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source)
      (fun y => ⟨y, mem_chart_source _ y⟩) (Real.sqrt_nonneg τ) γ hγ
      (fun k s => (paths k).curve (s ^ 2)) hlim
  obtain ⟨w, hw, hsum⟩ := K.finite_chart_limit_le_spatialInfimum p hτ paths hanti
    haction γ hγ hlim t ht hta htb x Q hQ
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source :=
    fun s hs => (hQ i).2.2 (interior_subset ((hQ i).2.1 (mem_image_of_mem γ hs)))
  obtain ⟨α, hα, hact, hminimal⟩ := K.exists_minimizing_path_of_regular_chart_limit hτ
    t ht hta htb γ hγ.continuousOn (hreg.of_le (by simp)) x hsrc w hw
    (by simpa only [chartH1Action, hγ0] using hsum)
  refine ⟨α, ?_, ?_, ?_⟩
  · simpa only [Real.sqrt_zero, hγ0] using hα 0
  · simpa only [hγ0] using hact
  · simpa only [hγ0] using hminimal

end PoincareConjecture.AncientKappaSolution
