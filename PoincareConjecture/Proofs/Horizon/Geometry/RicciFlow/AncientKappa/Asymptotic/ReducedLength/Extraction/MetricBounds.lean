import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.TimeIndependent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem IsSmoothFamilyOn.exists_uniform_coordinate_tangentNorm_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J) (hJ : IsOpen J)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hf : ∀ x ∈ A, ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    {I : Set ℝ} (hI : IsCompact I) (hIJ : I ⊆ J) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ I, ∀ x ∈ A,
      ∀ v : EuclideanSpace ℝ (Fin n),
        (g t).tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ B * ‖v‖ := by
  have hc : ContinuousOn
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (I ×ˢ A) := by
    intro p hp
    exact (hg.contDiffAt_spacetime_pullbackCoefficients hJ (hf p.2 hp.2)
      (hIJ hp.1)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (hI.prod hA).exists_bound_of_continuousOn
    (f := fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g p.1).pullbackCoefficients f p.2) hc
  refine ⟨Real.sqrt (max C 0), Real.sqrt_nonneg _, ?_⟩
  intro t ht x hx v
  have hnorm := ((g t).pullbackCoefficients f x).le_opNorm₂ v v
  have hcoeff := (hC (t, x) ⟨ht, hx⟩).trans (le_max_left C 0)
  have hinner : (g t).inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ max C 0 * ‖v‖ ^ 2 := by
    have h := (le_abs_self (((g t).pullbackCoefficients f x) v v)).trans
      (hnorm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg v)) (norm_nonneg v)))
    change (g t).inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ max C 0 * ‖v‖ * ‖v‖ at h
    simpa only [pow_two, mul_assoc] using h
  exact (Real.sqrt_le_sqrt hinner).trans_eq (by
    rw [Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq (norm_nonneg v)])

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem sourceCoordinateChart_tangentNorm_eq (G : PointedGeometricConvergence S)
    (hT : T' < 0 ∧ 0 < T) (k : ℕ) (q : G.limitCarrier.carrier)
    {t : ℝ} (ht : t ∈ Ioo T' T) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (G.sourceCoordinateChart hT k q).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
    letI : TopologicalSpace (S.carrier (G.subsequence k)).carrier :=
      (S.carrier (G.subsequence k)).topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier (G.subsequence k)).carrier :=
      (S.carrier (G.subsequence k)).chartedSpace
    letI : IsManifold (𝓡 n) ∞ (S.carrier (G.subsequence k)).carrier :=
      (S.carrier (G.subsequence k)).isManifold
    ((S.flow (G.subsequence k)).flow.metric t).tangentNorm
      (G.sourceCoordinateChart hT k q x)
      (mfderiv (𝓡 n) (𝓡 n) (G.sourceCoordinateChart hT k q) x v) =
    Real.sqrt (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k))
      (G.embedding k) t ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x v)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x v)) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : TopologicalSpace (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).chartedSpace
  let : IsManifold (𝓡 n) ∞ (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).isManifold
  let c := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let ψ : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun y => ((G.embedding k).toFun (t, y)).2
  have heq : (G.sourceCoordinateChart hT k q : _ → _) =ᶠ[𝓝 x] ψ ∘ c := by
    filter_upwards [(G.sourceCoordinateChart hT k q).open_source.mem_nhds hx] with y hy
    exact (G.embedding k).spatial_eq_of_mem hT ht hy.2
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c x :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_source.mem_nhds hx.1)
  have hψ : ContMDiffAt (𝓡 n) (𝓡 n) ∞ ψ (c x) :=
    (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) ht hx.2
  rw [RiemannianMetric.tangentNorm, heq.eq_of_nhds, heq.mfderiv_eq,
    mfderiv_comp x (hψ.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
  rfl

theorem exists_eventually_sourceCoordinateChart_tangentNorm_bound
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (q : G.limitCarrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
      A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {I : Set ℝ} (hI : IsCompact I) (hIT : I ⊆ Ioo T' T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      letI : TopologicalSpace (S.carrier (G.subsequence k)).carrier :=
        (S.carrier (G.subsequence k)).topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier (G.subsequence k)).carrier :=
        (S.carrier (G.subsequence k)).chartedSpace
      letI : IsManifold (𝓡 n) ∞ (S.carrier (G.subsequence k)).carrier :=
        (S.carrier (G.subsequence k)).isManifold
      A ⊆ (G.sourceCoordinateChart hT k q).source ∧
      ∀ t ∈ I, ∀ x ∈ A, ∀ v : EuclideanSpace ℝ (Fin n),
        ((S.flow (G.subsequence k)).flow.metric t).tangentNorm
          (G.sourceCoordinateChart hT k q x)
          (mfderiv (𝓡 n) (𝓡 n) (G.sourceCoordinateChart hT k q) x v) ≤ B * ‖v‖ := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let c := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  have hc : ∀ x ∈ A, ContMDiffAt (𝓡 n) (𝓡 n) ∞ c x := fun x hx =>
    contMDiffOn_chart_symm.contMDiffAt (c.open_source.mem_nhds (hchart hx))
  obtain ⟨B, hB, hb⟩ := G.limitFlow.flow.smooth.exists_uniform_coordinate_tangentNorm_bound
    isOpen_Ioo hA hc hI hIT
  refine ⟨2 * B, mul_nonneg (by norm_num) hB, ?_⟩
  have hK : IsCompact (c '' A) := hA.image_of_continuousOn
    (c.continuousOn.mono hchart)
  filter_upwards [G.eventually_subset_sourceCoordinateChart hT q hA hchart,
    G.eventually_pullback_tangentNorm_upper_on_compactTime hK hI hIT
      (by norm_num : (1 : ℝ) < 2)] with k hk hmetric
  let : TopologicalSpace (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).chartedSpace
  let : IsManifold (𝓡 n) ∞ (S.carrier (G.subsequence k)).carrier :=
    (S.carrier (G.subsequence k)).isManifold
  refine ⟨hk, ?_⟩
  intro t ht x hx v
  rw [G.sourceCoordinateChart_tangentNorm_eq hT k q (hIT ht) (hk hx) v]
  have h := hmetric t ht (c x) (mem_image_of_mem c hx) (mfderiv (𝓡 n) (𝓡 n) c x v)
  exact h.trans (by simpa only [FlowCarrier.metricNorm, FlowCarrier.metricInner,
    BasedFlow.metricAt, RiemannianMetric.tangentNorm, mul_assoc] using
    mul_le_mul_of_nonneg_left (hb t ht x hx v) (by norm_num : (0 : ℝ) ≤ 2))

end PoincareConjecture.PointedGeometricConvergence
