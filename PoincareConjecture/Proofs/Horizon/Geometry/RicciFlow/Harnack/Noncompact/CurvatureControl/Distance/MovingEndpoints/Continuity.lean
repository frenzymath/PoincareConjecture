import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Continuity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem continuousOn_backward_moving_distance
    (F : RicciFlow n M J) {a b : ℝ}
    (hJ : Icc (-b) (-a) ⊆ interior J)
    (hcomplete : MetricComplete (F.metric (-a)))
    (hRic : ∀ t ∈ Icc (-b) (-a), ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    {γ η : ℝ → M} (hγ : ContinuousOn γ (Icc a b)) (hη : ContinuousOn η (Icc a b)) :
    ContinuousOn (fun t => ((F.metric (-t)).edist (γ t) (η t)).toReal) (Icc a b) := by
  intro t ht
  have hfixed := F.continuousOn_toReal_edist_of_ricci_nonneg_intrinsic hJ hcomplete hRic (γ t)
  have hbase : ContinuousOn (fun s => ((F.metric (-s)).edist (γ t) (η s)).toReal)
      (Icc a b) :=
    hfixed.comp (continuous_neg.continuousOn.prodMk hη)
      (fun s hs => ⟨⟨neg_le_neg hs.2, neg_le_neg hs.1⟩, mem_univ _⟩)
  have herr : ContinuousOn (fun s => ((F.metric (-s)).edist (γ t) (γ s)).toReal)
      (Icc a b) :=
    hfixed.comp (continuous_neg.continuousOn.prodMk hγ)
      (fun s hs => ⟨⟨neg_le_neg hs.2, neg_le_neg hs.1⟩, mem_univ _⟩)
  have hzero : ((F.metric (-t)).edist (γ t) (γ t)).toReal = 0 := by
    let := (F.metric (-t)).toMetricSpace
    exact dist_self (γ t)
  have hlower := (hbase t ht).sub (herr t ht)
  have hupper := (hbase t ht).add (herr t ht)
  simp only [ContinuousWithinAt, Pi.sub_apply, hzero, sub_zero] at hlower
  simp only [ContinuousWithinAt, Pi.add_apply, hzero, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · exact Eventually.of_forall (fun s => by
      let := (F.metric (-s)).toMetricSpace
      change dist (γ t) (η s) - dist (γ t) (γ s) ≤ dist (γ s) (η s)
      linarith [dist_triangle (γ t) (γ s) (η s)])
  · exact Eventually.of_forall (fun s => by
      let := (F.metric (-s)).toMetricSpace
      change dist (γ s) (η s) ≤ dist (γ t) (η s) + dist (γ t) (γ s)
      have h := dist_triangle (γ s) (γ t) (η s)
      rw [dist_comm (γ s) (γ t)] at h
      linarith)

end PoincareConjecture.RicciFlow
