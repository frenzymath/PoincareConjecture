import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.Ellipticity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.Charts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem sourceCoordinateChart_pullbackCoefficients_eq (G : AncientCompactTimeConvergence S)
    (k : ℕ) (q : G.limit.carrier.carrier)
    (hk : ancientM18TimeWindow k ∈ 𝓝 (-1 : ℝ))
    {t : ℝ} (ht : ancientM18TimeWindow k ∈ 𝓝 t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (G.sourceCoordinateChart k q).source) :
    ((S.rescaling (G.subsequence k)).flow.metric t).pullbackCoefficients
      (G.sourceCoordinateChart k q) x = G.coordinateBilinear k q t x := by
  let c := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let ψ : G.limit.carrier.carrier → M := fun y => ((G.embedding k).toFun (t, y)).2
  have hx' : x ∈ c.source ∧ c x ∈ G.exhaustion k := by
    rw [sourceCoordinateChart, dif_pos hk] at hx
    exact hx
  have heq : (G.sourceCoordinateChart k q : _ → _) =ᶠ[𝓝 x] ψ ∘ c := by
    filter_upwards [(G.sourceCoordinateChart k q).open_source.mem_nhds hx] with y hy
    have hy' : y ∈ c.source ∧ c y ∈ G.exhaustion k := by
      rw [sourceCoordinateChart, dif_pos hk] at hy
      exact hy
    rw [G.sourceCoordinateChart_apply k q hk]
    exact G.sourcePoint_eq_at k (mem_of_mem_nhds ht) hy'.2
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c x :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_source.mem_nhds hx'.1)
  have hψ : ContMDiffAt (𝓡 n) (𝓡 n) ∞ ψ (c x) :=
    (G.embedding k).spatialMap_contMDiffAt_of_time_nhds (G.exhaustion_open k) ht hx'.2
  ext v w
  change ((S.rescaling (G.subsequence k)).flow.metric t).inner
    (G.sourceCoordinateChart k q x)
    (mfderiv (𝓡 n) (𝓡 n) (G.sourceCoordinateChart k q) x v)
    (mfderiv (𝓡 n) (𝓡 n) (G.sourceCoordinateChart k q) x w) = _
  rw [heq.eq_of_nhds, heq.mfderiv_eq,
    mfderiv_comp x (hψ.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
  rfl

theorem tendstoUniformlyOn_sourceCoordinateChart_pullbackCoefficients
    (G : AncientCompactTimeConvergence S) (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {τ : ℝ} (hτ : 0 < τ) :
    TendstoUniformlyOn
      (fun k x => ((S.rescaling (G.subsequence k)).flow.metric (-τ)).pullbackCoefficients
        (G.sourceCoordinateChart k q) x)
      (fun x => (G.limit.flow.metric (-τ)).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) atTop A := by
  have hchart' : A ⊆ (extChartAt (𝓡 n) q).target := by
    simpa only [extChartAt_target, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ] using hchart
  apply (G.tendstoUniformlyOn_coordinateBilinear q (neg_neg_of_pos hτ) hA hchart').congr
  filter_upwards [G.eventually_subset_sourceCoordinateChart q hA hchart,
    eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0),
    eventually_timeWindow_mem_nhds (neg_neg_of_pos hτ)] with k hk hbase ht x hx
  exact (G.sourceCoordinateChart_pullbackCoefficients_eq k q hbase ht (hk hx)).symm

theorem tendstoUniformlyOn_sourceCoordinateChart_volumeDensity
    (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {τ : ℝ} (hτ : 0 < τ) :
    TendstoUniformlyOn
      (fun k x => ((S.rescaling (G.subsequence k)).flow.metric (-τ)).pullbackVolumeDensity
        (G.sourceCoordinateChart k q) x)
      (fun x => (G.limit.flow.metric (-τ)).pullbackVolumeDensity
        (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) atTop A := by
  have hcont : ContinuousOn (fun x => (G.limit.flow.metric (-τ)).pullbackCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) A := by
    intro x hx
    exact ((G.limit.flow.metric (-τ)).contDiffAt_pullbackCoefficients
      (contMDiffOn_chart_symm.contMDiffAt
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).open_target.mem_nhds (hchart hx)))).continuousAt.continuousWithinAt
  simpa only [CoordinateMetric.density_pullbackCoefficients] using
    CoordinateMetric.tendstoUniformlyOn_density hA hcont
      (G.tendstoUniformlyOn_sourceCoordinateChart_pullbackCoefficients q hA hchart hτ)

theorem tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients
    (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {τ : ℝ} (hτ : 0 < τ) :
    TendstoUniformlyOn
      (fun k x => LeviCivitaData.Dirichlet.divergenceCoefficients
        ((S.rescaling (G.subsequence k)).flow.metric (-τ)) (G.sourceCoordinateChart k q) x)
      (fun x => LeviCivitaData.Dirichlet.divergenceCoefficients
        (G.limit.flow.metric (-τ)) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)
      atTop A := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
  have hcont : ContinuousOn (fun x => (G.limit.flow.metric (-τ)).pullbackCoefficients e x) A := by
    intro x hx
    exact ((G.limit.flow.metric (-τ)).contDiffAt_pullbackCoefficients
      (contMDiffOn_chart_symm.contMDiffAt
        (e.open_source.mem_nhds (hchart hx)))).continuousAt.continuousWithinAt
  simpa only [CoordinateMetric.divergenceMatrix_pullbackCoefficients] using
    CoordinateMetric.tendstoUniformlyOn_divergenceMatrix hA hcont
      (fun x hx => (G.limit.flow.metric (-τ)).isInvertible_pullbackCoefficients
        (hD.mfderiv_injective (hchart hx)))
      (G.tendstoUniformlyOn_sourceCoordinateChart_pullbackCoefficients q hA hchart hτ)

theorem exists_eventually_sourceCoordinateChart_uniform_ellipticity
    (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ x ∈ A, ∀ w : Fin n → ℝ,
      c * ∑ i, (w i) ^ 2 ≤ ∑ i, ∑ j,
        LeviCivitaData.Dirichlet.divergenceCoefficients
          ((S.rescaling (G.subsequence k)).flow.metric (-τ)) (G.sourceCoordinateChart k q) x i j *
            w j * w i := by
  apply CoordinateMetric.exists_eventually_uniform_ellipticity hA
    (A := fun x => LeviCivitaData.Dirichlet.divergenceCoefficients
      (G.limit.flow.metric (-τ)) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)
  · apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro l
    exact (LeviCivitaData.Dirichlet.contDiffOn_divergenceCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) q).symm contMDiffOn_chart_symm contMDiffOn_chart i l).continuousOn.mono hchart
  · intro x hx v hv
    have hp := LeviCivitaData.Dirichlet.divergenceCoefficients_pos
      (g := G.limit.flow.metric (-τ)) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
      contMDiffOn_chart_symm contMDiffOn_chart (hchart hx) v hv
    convert! hp using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  · exact G.tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients q hA hchart hτ

theorem exists_eventually_sourceCoordinateChart_coefficient_bounds
    (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ A,
      |((S.rescaling (G.subsequence k)).flow.metric (-τ)).pullbackVolumeDensity
        (G.sourceCoordinateChart k q) x| ≤ C ∧
      ∀ i l, |LeviCivitaData.Dirichlet.divergenceCoefficients
        ((S.rescaling (G.subsequence k)).flow.metric (-τ)) (G.sourceCoordinateChart k q) x i l| ≤ C := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let g := G.limit.flow.metric (-τ)
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) A := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (contMDiffOn_chart_symm.contMDiffAt (e.open_source.mem_nhds (hchart hx)))
      (hD.mfderiv_injective (hchart hx))).1.continuousAt.continuousWithinAt
  have hB : ContinuousOn (LeviCivitaData.Dirichlet.divergenceCoefficients g e) A := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro l
    exact (LeviCivitaData.Dirichlet.contDiffOn_divergenceCoefficients e
      contMDiffOn_chart_symm contMDiffOn_chart i l).continuousOn.mono hchart
  obtain ⟨Cρ, hCρ, hbρ⟩ := CoordinateMetric.exists_eventually_norm_le_of_compact_limit
    hA hρ (G.tendstoUniformlyOn_sourceCoordinateChart_volumeDensity q hA hchart hτ)
  obtain ⟨CB, hCB, hbB⟩ := CoordinateMetric.exists_eventually_norm_le_of_compact_limit
    hA hB (G.tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients q hA hchart hτ)
  refine ⟨Cρ + CB, add_nonneg hCρ hCB, ?_⟩
  filter_upwards [hbρ, hbB] with k hkρ hkB x hx
  refine ⟨?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using
      (hkρ x hx).trans (le_add_of_nonneg_right hCB)
  intro i l
  have hentry := (norm_le_pi_norm
    (LeviCivitaData.Dirichlet.divergenceCoefficients
      ((S.rescaling (G.subsequence k)).flow.metric (-τ)) (G.sourceCoordinateChart k q) x i) l).trans
      ((norm_le_pi_norm _ i).trans (hkB x hx))
  simpa only [Real.norm_eq_abs] using hentry.trans (le_add_of_nonneg_left hCρ)

end PoincareConjecture.AncientCompactTimeConvergence
