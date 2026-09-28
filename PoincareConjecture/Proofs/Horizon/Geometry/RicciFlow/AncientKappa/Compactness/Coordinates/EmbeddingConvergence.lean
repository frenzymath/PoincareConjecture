import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.EmbeddingBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.TerminalEventual
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.TimeShift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance embeddingConvergenceCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

theorem tendstoUniformlyOn_bilinear_jets_of_components
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℕ → X → SpacetimeBounds.MetricCoefficient 3)
    (g : X → SpacetimeBounds.MetricCoefficient 3) {K : Set X} (m : ℕ)
    (hf : ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, ContDiffAt ℝ ∞ (f k) z)
    (hg : ∀ z ∈ K, ContDiffAt ℝ ∞ g z)
    (hcomponent : ∀ a b : Fin 3, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (coefficientEval a b ∘ f k))
      (iteratedFDeriv ℝ m (coefficientEval a b ∘ g)) atTop K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
      (iteratedFDeriv ℝ m g) atTop K := by
  obtain ⟨D, hD, hnorm⟩ := exists_bilinear_jet_norm_le_components X m
  have hm : (m : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let η := ε / (2 * D)
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hD)
  have hc (a b : Fin 3) := Metric.tendstoUniformlyOn_iff.mp (hcomponent a b) η hη
  filter_upwards [hf, Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (hc a))]
    with k hk hkc z hz
  rw [dist_eq_norm]
  have hbound := hnorm (iteratedFDeriv ℝ m g z - iteratedFDeriv ℝ m (f k) z) η hη.le
    (fun a b => by
      have hd := (hkc a b z hz).le
      rw [dist_eq_norm, (coefficientEval a b).iteratedFDeriv_comp_left (hg z hz) hm,
        (coefficientEval a b).iteratedFDeriv_comp_left (hk z hz) hm] at hd
      have hsub : (coefficientEval a b).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m g z - iteratedFDeriv ℝ m (f k) z) =
          (coefficientEval a b).compContinuousMultilinearMap (iteratedFDeriv ℝ m g z) -
          (coefficientEval a b).compContinuousMultilinearMap (iteratedFDeriv ℝ m (f k) z) := by
        ext v
        exact map_sub (coefficientEval a b) _ _
      rw [hsub]
      exact hd)
  apply hbound.trans_lt
  dsimp [η]
  calc
    D * (ε / (2 * D)) = ε / 2 := by field_simp
    _ < ε := by linarith

variable {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
  (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
    (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

theorem embedding_coordinateCoefficient_eq_pullbackCoefficients_unshifted
    (q : G.limitCarrier.carrier) (k : ℕ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hxe : (extChartAt (𝓡 3) q).symm x ∈ G.exhaustion k) (a b : Fin 3) :
    G.limitCarrier.coordinateCoefficient q
      (fun s y v w => spatialPullbackInner G.limitCarrier
        (S.term (G.subsequence k)).carrier
        ((S.term (G.subsequence k)).flow.flow.metric s) (G.embedding k) y v w)
      a b (t, x) =
    ((S.term (G.subsequence k)).flow.flow.metric t).pullbackCoefficients
      (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) x
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) := by
  simpa only [FlowCarrier.coordinateCoefficient, add_sub_cancel_right] using
    S.embedding_coordinateCoefficient_eq_pullbackCoefficients G q k (t + 1) x hx hxe a b

theorem eventually_embedding_contDiffAt_originalTime
    (q : G.limitCarrier.carrier)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKt : ∀ z ∈ K, z.1 < 0)
    (hKc : ∀ z ∈ K, z.2 ∈ (extChartAt (𝓡 3) q).target) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, ContDiffAt ℝ ∞
      (fun w : ℝ × EuclideanSpace ℝ (Fin 3) =>
        ((S.term (G.subsequence k)).flow.flow.metric w.1).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) w.2) z := by
  have hKx : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  have hKxc : Prod.snd '' K ⊆ (extChartAt (𝓡 3) q).target := by
    rintro _ ⟨z, hz, rfl⟩
    exact hKc z hz
  filter_upwards [S.eventually_embedding_chart_isLocalDiffeomorphAt G q hKx hKxc]
    with k hk z hz
  let Fneg := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    (S.term (G.subsequence k)).flow.flow
    (show Iio (0 : ℝ) ⊆ Iic 0 from fun t ht => show t ≤ 0 from ht.le)
    ordConnected_Iio (show (Iio (0 : ℝ)).Nontrivial from
      ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩)
  exact Fneg.smooth.contDiffAt_spacetime_pullbackCoefficients isOpen_Iio
    (hk z.2 (mem_image_of_mem _ hz)).contMDiffAt (hKt z hz)

theorem interiorLimit_contDiffAt_pullbackCoefficients_unshifted
    (q : G.limitCarrier.carrier) (z : ℝ × EuclideanSpace ℝ (Fin 3))
    (ht : z.1 < 0) (hx : z.2 ∈ (extChartAt (𝓡 3) q).target) :
    ContDiffAt ℝ ∞ (fun w : ℝ × EuclideanSpace ℝ (Fin 3) =>
      (G.limitFlow.metric (w.1 + 1)).pullbackCoefficients
        (extChartAt (𝓡 3) q).symm w.2) z := by
  have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx).contMDiffAt
    (extChartAt_target_mem_nhds' hx)
  have hg := G.limitFlow.smooth.contDiffAt_spacetime_pullbackCoefficients isOpen_Iio hc
    (show z.1 + 1 ∈ Iio (1 : ℝ) by change z.1 + 1 < 1; linarith)
  exact hg.comp z ((contDiffAt_fst.add contDiffAt_const).prodMk contDiffAt_snd)

theorem tendstoUniformlyOn_embedding_bilinear_metricJet_unshifted
    (q : G.limitCarrier.carrier) (m : ℕ)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKt : ∀ z ∈ K, z.1 < 0)
    (hKc : ∀ z ∈ K, z.2 ∈ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun w : ℝ × EuclideanSpace ℝ (Fin 3) =>
        ((S.term (G.subsequence k)).flow.flow.metric w.1).pullbackCoefficients
          (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) w.2))
      (iteratedFDeriv ℝ m (fun w : ℝ × EuclideanSpace ℝ (Fin 3) =>
        (G.limitFlow.metric (w.1 + 1)).pullbackCoefficients
          (extChartAt (𝓡 3) q).symm w.2)) atTop K := by
  let c := extChartAt (𝓡 3) q
  let f := fun k (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
    ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
      (G.embedding k ∘ c.symm) z.2
  let g := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (G.limitFlow.metric (z.1 + 1)).pullbackCoefficients c.symm z.2
  apply tendstoUniformlyOn_bilinear_jets_of_components f g m
    (S.eventually_embedding_contDiffAt_originalTime G q hK hKt hKc)
    (fun z hz => S.interiorLimit_contDiffAt_pullbackCoefficients_unshifted G q z
      (hKt z hz) (hKc z hz))
  intro a b
  have hc : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ (Fin 3) => c.symm z.2) K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.comp
      continuous_snd.continuousOn hKc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨N, hjN, hN⟩ := S.interiorLimit_pullback_metric_CInfinity_unshifted G q j m K hK
    (fun z hz => ⟨hKt z hz, hKc z hz, hj (mem_image_of_mem _ hz)⟩) ε hε
  filter_upwards [eventually_ge_atTop N] with k hk z hz
  let fs := G.limitCarrier.coordinateCoefficient q
    (fun t x v w => spatialPullbackInner G.limitCarrier
      (S.term (G.subsequence k)).carrier ((S.term (G.subsequence k)).flow.flow.metric t)
      (G.embedding k) x v w) a b
  have heq : fs =ᶠ[𝓝 z] (coefficientEval a b ∘ f k) := by
    have hcx := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q (hKc z hz)).contMDiffAt
      (extChartAt_target_mem_nhds' (hKc z hz))
    filter_upwards [continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' (hKc z hz)),
      (hcx.continuousAt.comp continuousAt_snd).preimage_mem_nhds
        ((G.exhaustion_open k).mem_nhds (hmono (hjN.trans hk) (hj (mem_image_of_mem _ hz))))]
      with w hw hwe
    convert! S.embedding_coordinateCoefficient_eq_pullbackCoefficients_unshifted
      G q k w.1 w.2 hw hwe a b using 1
  have hlimit : G.limitCarrier.coordinateCoefficient q
      (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metric (t + 1)) x v w)
      a b = coefficientEval a b ∘ g := by
    funext w
    rfl
  have h := hN k hk a b z hz
  rw [hlimit, show iteratedFDeriv ℝ m fs z =
    iteratedFDeriv ℝ m (coefficientEval a b ∘ f k) z from
      (heq.iteratedFDeriv ℝ m).self_of_nhds] at h
  rw [dist_eq_norm, norm_sub_rev]
  exact h

theorem exists_smooth_terminal_embedding_coefficients
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (q : G.limitCarrier.carrier) {x₀ : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ} (hρ : 0 < ρ)
    (hchart : Metric.closedBall x₀ ρ ⊆ (extChartAt (𝓡 3) q).target) :
    ∃ B : ℝ × EuclideanSpace ℝ (Fin 3) → SpacetimeBounds.MetricCoefficient 3,
      ContDiffOn ℝ ∞ B (Iic 0 ×ˢ Metric.closedBall x₀ ρ) ∧
      ∀ m K, IsCompact K → K ⊆ Iic 0 ×ˢ Metric.closedBall x₀ ρ →
        TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m
            (fun w : ℝ × EuclideanSpace ℝ (Fin 3) =>
              ((S.term (G.subsequence k)).flow.flow.metric w.1).pullbackCoefficients
                (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) w.2)
            (Iic 0 ×ˢ Metric.closedBall x₀ ρ))
          (iteratedFDerivWithin ℝ m B (Iic 0 ×ˢ Metric.closedBall x₀ ρ)) atTop K := by
  let f := fun k (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
    ((S.term (G.subsequence k)).flow.flow.metric z.1).pullbackCoefficients
      (G.embedding k ∘ (extChartAt (𝓡 3) q).symm) z.2
  let g := fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (G.limitFlow.metric (z.1 + 1)).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2
  let Ω : Set (ℝ × EuclideanSpace ℝ (Fin 3)) := Iic 0 ×ˢ Metric.closedBall x₀ ρ
  have hconvex : Convex ℝ Ω := (convex_Iic 0).prod (convex_closedBall x₀ ρ)
  have hne : (interior Ω).Nonempty := by
    rw [show Ω = Iic 0 ×ˢ Metric.closedBall x₀ ρ from rfl,
      interior_prod_eq, interior_Iic, interior_closedBall x₀ hρ.ne']
    exact ⟨(-1, x₀), by simp [hρ]⟩
  have hunique := uniqueDiffOn_convex hconvex hne
  apply AncientCompactness.exists_smooth_terminal_limit_same_sequence_of_eventually hρ f
    (S.eventually_embedding_contDiffOn_terminal G q hchart)
    (fun m => iteratedFDeriv ℝ m g) ?_ ?_
  · intro m K hK hKU
    have hKt (z) (hz : z ∈ K) : z.1 < 0 := (hKU hz).1
    have hKc (z) (hz : z ∈ K) : z.2 ∈ (extChartAt (𝓡 3) q).target := hchart (hKU hz).2
    have hconv := S.tendstoUniformlyOn_embedding_bilinear_metricJet_unshifted G q m hK hKt hKc
    apply hconv.congr
    filter_upwards [S.eventually_embedding_contDiffAt_originalTime G q hK hKt hKc]
      with k hk z hz
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hunique
      ((hk z hz).of_le (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)))
      ⟨(hKt z hz).le, (hKU hz).2⟩).symm
  · intro K hK hKΩ m
    exact S.exists_eventually_embedding_terminal_jet_bound G P hcontrol hcomplete q hρ hchart hK hKΩ m

end PoincareConjecture.NormalizedKappaSolutionSequence
