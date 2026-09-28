import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.ScalarNormalized












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]



theorem eventually_movingTime_scalarNormalized_centeredNeck_jets_full_domain
    (F : RicciFlow 3 M (Iic 0)) (N : EpsilonNeck (F.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {κ : Type*} {l : Filter κ} {r : ℝ} (hr : 0 < r)
    {s : κ → ℝ} (hs : Tendsto s l (𝓝 r))
    (tau : κ → ℝ) (htau : ∀ k, tau k ∈ Icc (-1 : ℝ) 0)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in l, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun y =>
          s k • (F.metric (tau k / s k)).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y -
          r • (F.metric (tau k / r)).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y) 0‖ ≤ eta := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E _
  let m := ⌊N.epsilon⁻¹⌋₊
  have hm : 1 ≤ m := by
    have htwo := N.two_le_floor_inv_epsilon
    omega
  have hlocal (q : M) :
      ∃ U ∈ 𝓝 q, ∀ᶠ k in l, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → N.coordinate_map z ∈ U →
        ∀ j : ℕ, j ≤ m →
          ‖iteratedFDeriv ℝ j (fun y =>
            s k • (F.metric (tau k / s k)).parametrizedCoefficients
              (centeredNeckLift N z.1 z.2) y -
            r • (F.metric (tau k / r)).parametrizedCoefficients
              (centeredNeckLift N z.1 z.2) y) 0‖ ≤ eta := by
    obtain ⟨K, hKnhds, hKchart, hK⟩ := local_compact_nhds
      ((isOpen_extChartAt_source (I := 𝓡 3) q).mem_nhds (mem_extChartAt_source q))
    obtain ⟨C, hC, hCj⟩ := exists_centeredNeckAmbientCoordinates_jet_bound
      N hsmall q hK hKchart m hm le_rfl
    let Z := {z : RoundCylinderSpace //
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧ N.coordinate_map z ∈ K}
    let f := fun z : Z => centeredNeckLift N z.1.1 z.1.2
    have hf (z : Z) : ∃ U, IsOpen U ∧ (0 : E) ∈ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f z) U := by
      refine ⟨centeredNeckDomain N z.1.2, centeredNeckDomain_isOpen N z.1.2,
        zero_mem_centeredNeckDomain N z.2.1, ?_⟩
      intro y hy
      exact (centeredNeckLift_contMDiffAt N z.1.1 z.1.2 hy).contMDiffWithinAt
    have hmap (z : Z) : f z 0 ∈ K := by
      simpa only [f, centeredNeckLift_zero] using z.2.2
    have hj (z : Z) (j : ℕ) (_hj₀ : 1 ≤ j) (hj : j ≤ m + 1) :
        ‖iteratedFDeriv ℝ j ((extChartAt (𝓡 3) q) ∘ f z) 0‖ ≤ C :=
      hCj z z.2.1 z.2.2 j hj
    refine ⟨K, hKnhds, ?_⟩
    filter_upwards [F.eventually_scalarNormalized_parametrized_jets_at_of_chart_bound
      q hK hKchart f hf hmap m hC hj hr hs tau htau heta] with k hk z hz hKz j hj
    exact hk ⟨z, hz, hKz⟩ j hj
  choose U hU hbound using hlocal
  obtain ⟨t, _, ht⟩ := hcompact.elim_nhds_subcover U (fun q _ => hU q)
  filter_upwards [t.eventually_all.mpr (fun q _ => hbound q)] with k hk z hz j hj
  have hzcarrier : N.coordinate_map z ∈ closure N.carrier :=
    subset_closure (neck_coordinate_mem N z ⟨mem_univ _, hz⟩)
  obtain ⟨q, hqt, hzq⟩ := mem_iUnion₂.mp (ht hzcarrier)
  exact hk q hqt z hz hzq j hj



theorem eventually_scalarNormalized_centeredNeck_jets_full_domain_uniform_time
    (F : RicciFlow 3 M (Iic 0)) (N : EpsilonNeck (F.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {κ : Type*} {l : Filter κ} {r : ℝ} (hr : 0 < r)
    {s : κ → ℝ} (hs : Tendsto s l (𝓝 r)) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in l, ∀ u ∈ Icc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun y =>
          s k • (F.metric (u / s k)).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y -
          r • (F.metric (u / r)).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y) 0‖ ≤ eta := by
  classical
  let Q (k : κ) (u : ℝ) : Prop := ∀ z : RoundCylinderSpace,
    z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
    ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
      ‖iteratedFDeriv ℝ j (fun y =>
        s k • (F.metric (u / s k)).parametrizedCoefficients
          (centeredNeckLift N z.1 z.2) y -
        r • (F.metric (u / r)).parametrizedCoefficients
          (centeredNeckLift N z.1 z.2) y) 0‖ ≤ eta
  let tau (k : κ) : ℝ :=
    if h : ∃ u ∈ Icc (-1 : ℝ) 0, ¬ Q k u then Classical.choose h else 0
  have htau (k : κ) : tau k ∈ Icc (-1 : ℝ) 0 := by
    dsimp only [tau]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · constructor <;> norm_num
  have hgood : ∀ᶠ k in l, Q k (tau k) :=
    F.eventually_movingTime_scalarNormalized_centeredNeck_jets_full_domain
      N hcompact hsmall hr hs tau htau heta
  change ∀ᶠ k in l, ∀ u ∈ Icc (-1 : ℝ) 0, Q k u
  filter_upwards [hgood] with k hk u hu
  by_contra hQu
  have hbad : ∃ u ∈ Icc (-1 : ℝ) 0, ¬ Q k u := ⟨u, hu, hQu⟩
  have hchosen : ¬ Q k (tau k) := by
    simpa only [tau, dif_pos hbad] using (Classical.choose_spec hbad).2
  exact hchosen hk

end PoincareConjecture.RicciFlow
