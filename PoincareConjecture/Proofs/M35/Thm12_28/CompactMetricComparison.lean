import PoincareConjecture.Proofs.M35.Thm12_28.TerminalMetricComparison
import PoincareConjecture.Proofs.M35.Thm12_28.MetricChartCancellation









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem eventually_on_compact {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {R : ℕ → X → Prop}
    (hlocal : ∀ x ∈ K, ∃ U ∈ 𝓝 x, ∀ᶠ k in atTop, ∀ y ∈ U, R k y) :
    ∀ᶠ k in atTop, ∀ y ∈ K, R k y := by
  apply hK.induction_on (p := fun S : Set X => ∀ᶠ k in atTop, ∀ y ∈ S, R k y)
  · exact Eventually.of_forall (fun _ _ hy => hy.elim)
  · intro S T hST hT
    exact hT.mono (fun _ hk y hy => hk y (hST hy))
  · intro S T hS hT
    filter_upwards [hS, hT] with k hkS hkT y hy
    exact hy.elim (hkS y) (hkT y)
  · intro x hx
    obtain ⟨U, hUx, hU⟩ := hlocal x hx
    exact ⟨U, mem_nhdsWithin_of_mem_nhds hUx, hU⟩




theorem blowupSequence_compact_metric_comparison (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (j : ℕ) (K : Set L.limit.sliceCarrier.carrier) (hK : IsCompact K)
    (hKU : K ⊆ L.exhaustion.space j) (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ y ∈ K, ∀ v : TangentSpace (𝓡 3) y,
      let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
        fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      |(blowupSequence P E t x ht hR).scale (L.subsequence k) *
        (E.flow.metric (t (L.subsequence k))).inner (f y)
          (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y v) -
        (L.limit.flow.metric 0).inner y v v| ≤ eta * (L.limit.flow.metric 0).inner y v v := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  let f (k : ℕ) : L.limit.sliceCarrier.carrier → StandardCapSpace :=
    fun z => ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  let Good (k : ℕ) (y : L.limit.sliceCarrier.carrier) :=
    ∀ v : TangentSpace (𝓡 3) y,
      |(blowupSequence P E t x ht hR).scale (L.subsequence k) *
        (E.flow.metric (t (L.subsequence k))).inner (f k y)
          (mfderiv (𝓡 3) (𝓡 3) (f k) y v) (mfderiv (𝓡 3) (𝓡 3) (f k) y v) -
        (L.limit.flow.metric 0).inner y v v| ≤ eta * (L.limit.flow.metric 0).inner y v v
  have hevent : ∀ᶠ k in atTop, ∀ y ∈ K, Good k y := by
    apply eventually_on_compact hK
    intro q hq
    let c := extChartAt (𝓡 3) q
    let V := c.target ∩ c.symm ⁻¹' L.exhaustion.space j
    have hV : IsOpen V := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q) (L.exhaustion.space_open j)
    have hqV : c q ∈ V := ⟨mem_extChartAt_target q,
      (congrArg (fun z : L.limit.sliceCarrier.carrier => z ∈ L.exhaustion.space j)
        (c.left_inv (mem_extChartAt_source q))).mpr (hKU hq)⟩
    obtain ⟨C, hC, hqC, hCV⟩ := exists_compact_between isCompact_singleton hV
      (singleton_subset_iff.mpr hqV)
    let W := c.source ∩ c ⁻¹' interior C
    have hchartsource : c.source = (chartAt (EuclideanSpace ℝ (Fin 3)) q).source :=
      extChartAt_source (𝓡 3) q
    have hccont : ContinuousOn c c.source := hchartsource.symm ▸
      (contMDiffOn_extChartAt (I := 𝓡 3) (n := ∞) (x := q)).continuousOn
    have hW : IsOpen W := hccont.isOpen_inter_preimage
      (isOpen_extChartAt_source q) isOpen_interior
    have hqW : q ∈ W := ⟨mem_extChartAt_source q, hqC (mem_singleton _)⟩
    obtain ⟨N, hjN, hN⟩ := blowupSequence_terminal_metric_comparison P E t x ht hR L q j C hC
      (fun z hz => hCV hz) eta heta
    refine ⟨W, hW.mem_nhds hqW, ?_⟩
    filter_upwards [eventually_ge_atTop N] with k hk y hy
    intro v
    have hcy : c y ∈ C := interior_subset hy.2
    have hyj : y ∈ L.exhaustion.space j := (c.left_inv hy.1) ▸ (hCV hcy).2
    have hyk := L.exhaustion.space_increasing (hjN.trans hk) hyj
    have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
    have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
    have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f k) y :=
      ((sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
        ((L.embedding k).forward_smooth 0 hzero)).contMDiffAt
          ((L.exhaustion.space_open k).mem_nhds hyk)
    have hsource := (E.flow.metric (t (L.subsequence k))).pullbackCoefficients_chart_cancel
      (f k) q hy.1 hf v v
    have hlimit := (L.limit.flow.metric 0).chartCoefficients_cancel q hy.1 v v
    have hcompare := hN k hk (c y) hcy (mfderiv (𝓡 3) (𝓡 3) c y v)
    exact (congrArg₂ (fun a b : ℝ =>
      |(blowupSequence P E t x ht hR).scale (L.subsequence k) * a - b| ≤ eta * b)
      hsource hlimit).mp hcompare
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨max j N, le_max_left _ _, fun k hk => hN k ((le_max_right _ _).trans hk)⟩

end PoincareConjecture.M35.OrdinaryRealization
