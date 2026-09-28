import PoincareConjecture.Proofs.M47.LimitFiniteEndpointExtraction
import PoincareConjecture.Proofs.M47.TerminalGermsMetricRealization
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.LocalFlows









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteEndpointFlowDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointFlowDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteEndpointFlowBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointFlowBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace



theorem limitFinite_endpoint_chart_flow
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {T d R ρ a : ℝ} (hd : 0 < d) (hc : -T + d / 4 ≤ 0)
    (hρ : 0 < ρ) (hρR : ρ < R) (ha : 0 < a)
    (A : ℕ → RicciFlow 3 M (Icc (-(T + d / 2)) 0))
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (hsource : Φ.source = Metric.ball 0 R)
    (B : ℝ × E → V)
    (hB : ContDiffOn ℝ ∞ B (Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 ρ))
    (hsymm : ∀ p ∈ Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 ρ,
      ∀ v w, B p v w = B p w v)
    (hlower : ∀ p ∈ Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 ρ,
      ∀ v, a * ‖v‖ ^ 2 ≤ B p v v)
    (hjets : ∀ m C, IsCompact C →
      C ⊆ Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 ρ → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun p : ℝ × E =>
          ((A k).metric (p.1 + (-T + d / 4))).pullbackCoefficients Φ p.2))
        (iteratedFDeriv ℝ m B) atTop C) :
    let W := fun _ : Unit => Metric.ball (0 : E) ρ
    let hW : ∀ i, IsOpen (W i) := fun _ => Metric.isOpen_ball
    letI : Nonempty (W ()) := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
    letI := (hW ()).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hW ()).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∃ F : RicciFlow 3 (Piece W ()) (Ioo (-T - d / 8) (-T + d / 4)),
      -T ∈ Ioo (-T - d / 8) (-T + d / 4) ∧
      ∀ t ∈ Ioo (-T - d / 8) (-T + d / 4), ∀ (x : Piece W ()) v w,
        (F.metric t).inner x v w = B (t - (-T + d / 4), x) v w := by
  classical
  let W := fun _ : Unit => Metric.ball (0 : E) ρ
  let hW : ∀ i, IsOpen (W i) := fun _ => Metric.isOpen_ball
  let : Nonempty (W ()) := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let : ∀ i, Nonempty (Piece W i) := fun _ => ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let := (hW ()).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hW ()).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  let J := Ioo (-((3 * d / 4) / 2)) 0
  let c := -T + d / 4
  have ht0 : -d / 4 ∈ J := ⟨by linarith, by linarith⟩
  obtain ⟨g0, hg0⟩ := ChartDistance.exists_canonicalMetric_of_coordinate_limit W hW
    (fun _ z => B (-d / 4, z)) (fun z => B (-d / 4, z)) ()
    (hB.comp (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨ht0, hz⟩))
    (fun _ z hz v w => hsymm (-d / 4, z) ⟨ht0, hz⟩ v w)
    (fun _ _ _ _ => tendsto_const_nhds)
    (fun z hz => ⟨a, ha, Eventually.of_forall fun _ v => hlower (-d / 4, z) ⟨ht0, hz⟩ v⟩)
  obtain ⟨g, hg, hcoeff, _hg0⟩ := terminalGerms_realize_chart_metric W hW () ht0
    (fun _ => B) B hB (fun _ t ht z hz v w => hsymm (t, z) ⟨ht, hz⟩ v w)
    (fun _ _ _ _ _ _ => tendsto_const_nhds)
    (fun t ht z hz => ⟨a, ha, Eventually.of_forall fun _ v => hlower (t, z) ⟨ht, hz⟩ v⟩)
    g0 hg0
  let e : Piece W () → M := fun x => Φ x
  have he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := by
    intro x
    have hx : (x : E) ∈ Φ.source := by
      rw [hsource]
      exact Metric.ball_subset_ball hρR.le x.property
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) (W ()) (hW ()) ∞ x).comp
      (𝓡 3) M (Φ.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx)
  have hnear (z : E) (hz : z ∈ W ()) :
      ChartDistance.chartParametrization W hW e =ᶠ[𝓝 z] Φ := by
    filter_upwards [(hW ()).mem_nhds hz] with y hy
    exact ChartDistance.chartParametrization_apply W hW e ⟨y, hy⟩
  have hmap : (fun s : ℝ => s + c) '' J ⊆ Icc (-(T + d / 2)) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    dsimp [J, c] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]
  have hne : J.Nontrivial := by
    exact ⟨-d / 4, ht0, -d / 8, ⟨by linarith, by linarith⟩, by linarith⟩
  let A' : ℕ → RicciFlow 3 M J := fun k => (A k).translate c hmap ordConnected_Ioo hne
  have hactual (k : ℕ) : EqOn
      (fun p : ℝ × E => ((A k).metric (p.1 + c)).pullbackCoefficients Φ p.2)
      (fun p : ℝ × E => ((A' k).metric p.1).pullbackCoefficients
        (ChartDistance.chartParametrization W hW e) p.2) (J ×ˢ W ()) := by
    intro p hp
    have hn := hnear p.2 hp.2
    change ((A k).metric (p.1 + c)).pullbackCoefficients Φ p.2 =
      ((A k).metric (p.1 + c)).pullbackCoefficients
        (ChartDistance.chartParametrization W hW e) p.2
    unfold RiemannianMetric.pullbackCoefficients
    rw [hn.self_of_nhds, hn.mfderiv_eq]
  have hjetActual : ∀ m C, IsCompact C → C ⊆ J ×ˢ W () → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p : ℝ × E =>
        ((A' k).metric p.1).pullbackCoefficients
          (ChartDistance.chartParametrization W hW e) p.2))
      (iteratedFDeriv ℝ m B) atTop C := by
    intro m C hC hCΩ
    exact (hjets m C hC hCΩ).congr (Eventually.of_forall fun k =>
      (Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
        (isOpen_Ioo.prod (hW ())) (hactual k) m).mono hCΩ)
  obtain ⟨Fchart, hFchart⟩ := ChartDistance.exists_ricciFlow_on_coordinate_limit W hW
    isOpen_Ioo A' () (fun _ => e) (fun _ => he) g hg B hcoeff hjetActual
  let Jraw := Ioo (-T - d / 8) (-T + d / 4)
  have hrawmap : (fun t : ℝ => t + -c) '' Jraw ⊆ J := by
    rintro _ ⟨t, ht, rfl⟩
    dsimp [Jraw, J, c] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hrawne : Jraw.Nontrivial := by
    exact ⟨-T, ⟨by linarith, by linarith⟩, -T + d / 8,
      ⟨by linarith, by linarith⟩, by linarith⟩
  let F := Fchart.translate (-c) hrawmap ordConnected_Ioo hrawne
  refine ⟨F, ⟨by linarith, by linarith⟩, ?_⟩
  intro t ht x v w
  change (Fchart.metric (t + -c)).inner x v w = B (t - c, x) v w
  rw [hFchart]
  simpa only [sub_eq_add_neg] using hcoeff (t + -c) (hrawmap ⟨t, ht, rfl⟩) x v w

end PoincareConjecture.M47
