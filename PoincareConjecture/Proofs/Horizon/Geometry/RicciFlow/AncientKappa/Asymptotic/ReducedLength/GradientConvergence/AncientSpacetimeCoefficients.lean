import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.GradientConvergence.AncientCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Smooth


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

theorem tendstoUniformlyOn_coordinateBilinear_spacetime
    (G : AncientCompactTimeConvergence S) (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (extChartAt (𝓡 n) q).target)
    {s t : ℝ} (hst : s ≤ t) (ht : t < 0) :
    TendstoUniformlyOn (fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
      G.coordinateBilinear k q z.1 z.2)
      (fun z => (G.limit.flow.metric z.1).pullbackCoefficients
        (extChartAt (𝓡 n) q).symm z.2) atTop (Icc s t ×ˢ A) := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hc : IsCompact ((extChartAt (𝓡 n) q).symm '' A) :=
    hA.image_of_continuousOn ((contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hchart)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hc
  obtain ⟨m, hms, hmt⟩ := ((eventually_timeWindow_mem_nhds (hst.trans_lt ht)).and
    (eventually_timeWindow_mem_nhds ht)).exists
  let i := max j m
  have hdom : Icc s t ×ˢ A ⊆ {z | z.1 ∈ ancientM18TimeWindow i ∧
      z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion i} := by
    intro z hz
    have hztime : z.1 ∈ ancientM18TimeWindow m :=
      ⟨(mem_of_mem_nhds hms).1.trans hz.1.1, hz.1.2.trans (mem_of_mem_nhds hmt).2⟩
    exact ⟨ancientM18TimeWindow_mono (le_max_right j m) hztime, hchart hz.2,
      G.exhaustion_monotone (le_max_left j m) (hj (mem_image_of_mem _ hz.2))⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / ((n : ℝ) ^ 2 + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q i 0 (Icc s t ×ˢ A)
    (isCompact_Icc.prod hA) hdom δ hδ
  filter_upwards [eventually_ge_atTop N] with k hk z hz
  have hentry (a b : Fin n) :
      |(G.coordinateBilinear k q z.1 z.2 -
        (G.limit.flow.metric z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2)
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)| ≤ δ := by
    have hh := (hN k hk a b z hz).le
    change |ancientPullbackCoefficient (G.embedding k) q a b z -
      G.limit.carrier.coordinateCoefficient q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b z| ≤ δ
    simpa only [MetricJet, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      ← map_sub, LinearIsometryEquiv.norm_map, Real.norm_eq_abs] using hh
  have hh := HarmonicCoordinates.norm_bilinear_le_dim_sq_mul_of_entries _ hδ.le hentry
  have hsmall : (n : ℝ) ^ 2 * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ (by positivity : 0 < (n : ℝ) ^ 2 + 1)).mpr (by nlinarith)
  simpa only [dist_eq_norm, norm_sub_rev] using hh.trans_lt hsmall

theorem eventually_timeWindow_mem_nhds_on_backward_interval
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∀ᶠ k : ℕ in atTop, ∀ τ ∈ Icc α β, ancientM18TimeWindow k ∈ 𝓝 (-τ) := by
  filter_upwards [eventually_timeWindow_mem_nhds (neg_neg_of_pos hα),
    eventually_timeWindow_mem_nhds (neg_neg_of_pos (hα.trans_le hαβ))] with k hkα hkβ τ hτ
  have ha := Icc_mem_nhds_iff.mp hkα
  have hb := Icc_mem_nhds_iff.mp hkβ
  exact Icc_mem_nhds (by linarith [hb.1, hτ.2]) (by linarith [ha.2, hτ.1])

theorem tendstoUniformlyOn_sourceCoordinateChart_pullbackCoefficients_spacetime
    (G : AncientCompactTimeConvergence S) (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    TendstoUniformlyOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × ℝ) =>
        ((S.rescaling (G.subsequence k)).flow.metric (-z.2)).pullbackCoefficients
          (G.sourceCoordinateChart k q) z.1)
      (fun z => (G.limit.flow.metric (-z.2)).pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1) atTop (A ×ˢ Icc α β) := by
  have hchart' : A ⊆ (extChartAt (𝓡 n) q).target := by
    simpa only [extChartAt_target, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ] using hchart
  have h := (G.tendstoUniformlyOn_coordinateBilinear_spacetime q hA hchart'
    (neg_le_neg hαβ) (neg_neg_of_pos hα)).comp
      (fun z : EuclideanSpace ℝ (Fin n) × ℝ => (-z.2, z.1))
  have hm : A ×ˢ Icc α β ⊆ (fun z : EuclideanSpace ℝ (Fin n) × ℝ => (-z.2, z.1)) ⁻¹'
      (Icc (-β) (-α) ×ˢ A) := fun z hz => ⟨⟨neg_le_neg hz.2.2, neg_le_neg hz.2.1⟩, hz.1⟩
  apply (h.mono hm).congr
  filter_upwards [G.eventually_subset_sourceCoordinateChart q hA hchart,
    eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0),
    eventually_timeWindow_mem_nhds_on_backward_interval hα hαβ] with k hk hbase ht z hz
  exact (G.sourceCoordinateChart_pullbackCoefficients_eq k q hbase (ht z.2 hz.2)
    (hk hz.1)).symm

theorem tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients_spacetime
    (G : AncientCompactTimeConvergence S) (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    TendstoUniformlyOn
      (fun k (z : EuclideanSpace ℝ (Fin n) × ℝ) =>
        LeviCivitaData.Dirichlet.divergenceCoefficients
          ((S.rescaling (G.subsequence k)).flow.metric (-z.2))
          (G.sourceCoordinateChart k q) z.1)
      (fun z => LeviCivitaData.Dirichlet.divergenceCoefficients
        (G.limit.flow.metric (-z.2)) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm z.1)
      atTop (A ×ˢ Icc α β) := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
  have hdom : A ×ˢ Icc α β ⊆ RicciFlow.BackwardCoordinates.domain (Iio 0) e := by
    intro z hz
    exact ⟨hchart hz.1, by simpa only [interior_Iio, mem_preimage, mem_Iio] using neg_neg_of_pos (hα.trans_le hz.2.1)⟩
  have hcont := (RicciFlow.BackwardCoordinates.contDiffOn_pullbackCoefficients
    G.limit.flow e contMDiffOn_chart_symm contMDiffOn_chart).continuousOn.mono hdom
  simpa only [CoordinateMetric.divergenceMatrix_pullbackCoefficients] using
    CoordinateMetric.tendstoUniformlyOn_divergenceMatrix (hA.prod isCompact_Icc) hcont
      (fun z hz => (G.limit.flow.metric (-z.2)).isInvertible_pullbackCoefficients
        (hD.mfderiv_injective (hchart hz.1)))
      (G.tendstoUniformlyOn_sourceCoordinateChart_pullbackCoefficients_spacetime
        q hA hchart hα hαβ)

theorem exists_eventually_sourceCoordinateChart_spacetime_coefficient_bound
    (G : AncientCompactTimeConvergence S) (q : G.limit.carrier.carrier)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ z ∈ A ×ˢ Icc α β, ∀ i j,
      |LeviCivitaData.Dirichlet.divergenceCoefficients
        ((S.rescaling (G.subsequence k)).flow.metric (-z.2))
        (G.sourceCoordinateChart k q) z.1 i j| ≤ C := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  have hdom : A ×ˢ Icc α β ⊆ RicciFlow.BackwardCoordinates.domain (Iio 0) e := by
    intro z hz
    exact ⟨hchart hz.1, by simpa only [interior_Iio, mem_preimage, mem_Iio] using neg_neg_of_pos (hα.trans_le hz.2.1)⟩
  have hcont : ContinuousOn (fun z => LeviCivitaData.Dirichlet.divergenceCoefficients
      (G.limit.flow.metric (-z.2)) e z.1) (A ×ˢ Icc α β) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (RicciFlow.BackwardCoordinates.contDiffOn_weightedPrincipal G.limit.flow e
      contMDiffOn_chart_symm contMDiffOn_chart i j).continuousOn.mono hdom
  obtain ⟨C, hC, hb⟩ := CoordinateMetric.exists_eventually_norm_le_of_compact_limit
    (hA.prod isCompact_Icc) hcont
      (G.tendstoUniformlyOn_sourceCoordinateChart_divergenceCoefficients_spacetime
        q hA hchart hα hαβ)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with k hk z hz i j
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans (hk z hz))

end PoincareConjecture.AncientCompactTimeConvergence
