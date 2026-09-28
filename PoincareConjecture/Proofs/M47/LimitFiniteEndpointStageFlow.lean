import PoincareConjecture.Proofs.M47.LimitFiniteEndpointDescent
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointChartMaps
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointOriginalCover
import PoincareConjecture.Proofs.M47.TerminalGermsOpenMetrics
import PoincareConjecture.Proofs.M47.TerminalGermsOpenReadout
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Gluing
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteEndpointStageTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteEndpointStageCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteEndpointStageManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

variable (m j N : ℕ) (d : ℝ)

local notation "U" => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j)
local notation "V" => TopologicalSpace.Opens.mk
  (G.exhaustion.space m) (G.exhaustion.space_open m)
local notation "J" => Ioo (-H.toReal - d / 8) (-H.toReal + d / 4)



theorem limitFinite_endpoint_original_stage_flow (hd : 0 < d)
    (R ρ : Fin (N + 1) → ℝ) (hρ : ∀ i, 0 < ρ i) (hρR : ∀ i, ρ i < R i)
    (Φ : Fin (N + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (hsource : ∀ i, (Φ i).source = Metric.ball 0 (R i))
    (hcover : closure (G.exhaustion.space m) ⊆
      ⋃ i, (fun z : E => (Φ i z).val) '' Metric.ball 0 (ρ i))
    (B : Fin (N + 1) → ℝ × E → Bilin) :
    let W := fun i => Metric.ball (0 : E) (ρ i)
    let hW : ∀ i, IsOpen (W i) := fun _ => Metric.isOpen_ball
    letI : ∀ i, Nonempty (Piece W i) := fun i => ⟨⟨0, Metric.mem_ball_self (hρ i)⟩⟩
    letI : ∀ i, ChartedSpace E (Piece W i) :=
      fun i => (hW i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ i, IsManifold (𝓡 3) ∞ (Piece W i) :=
      fun i => (hW i).isOpenEmbedding_subtypeVal.isManifold_singleton
    let q : ∀ i, Piece W i → G.limit.sliceCarrier.carrier := fun i x => (Φ i x).val
    ∀ F : ∀ i, RicciFlow 3 (Piece W i) J,
      (∀ t ∈ J, ∀ i (x : Piece W i) (v w : E),
        ((F i).metric t).inner x v w = B i (t - (-H.toReal + d / 4), x) v w) →
      (∀ t ∈ J, ∀ i l (x : Piece W i) (y : Piece W l),
        (Φ i x).val = (Φ l y).val → ∀ a b c e : E,
          mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) (Φ i x)
              (mfderiv (𝓡 3) (𝓡 3) (Φ i) (x : E) a) =
            mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) (Φ l y)
              (mfderiv (𝓡 3) (𝓡 3) (Φ l) (y : E) c) →
          mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) (Φ i x)
              (mfderiv (𝓡 3) (𝓡 3) (Φ i) (x : E) b) =
            mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) (Φ l y)
              (mfderiv (𝓡 3) (𝓡 3) (Φ l) (y : E) e) →
          B i (t - (-H.toReal + d / 4), x) a b =
            B l (t - (-H.toReal + d / 4), y) c e) →
      (∀ t ∈ J, t ∈ blowupBackwardInterval H → ∀ i (x : Piece W i),
        B i (t - (-H.toReal + d / 4), x) =
          ((G.limit.flow.metric t).pullbackOfLocalDiffeomorph
            (Subtype.val : U → G.limit.sliceCarrier.carrier)
            (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U)).pullbackCoefficients
              (Φ i) x) →
      ∃ A : RicciFlow 3 V J, -H.toReal ∈ J ∧
        (∀ t ∈ J, ∀ i (x : Piece W i) (hx : q i x ∈ V) (v w : E),
          ((F i).metric t).inner x v w = (A.metric t).inner ⟨q i x, hx⟩
            (mfderiv (𝓡 3) (𝓡 3) (q i) x v)
            (mfderiv (𝓡 3) (𝓡 3) (q i) x w)) ∧
        ∀ t ∈ J, t ∈ blowupBackwardInterval H → ∀ (x : V) (v w : E),
          (A.metric t).inner x v w = (G.limit.flow.metric t).inner x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → G.limit.sliceCarrier.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → G.limit.sliceCarrier.carrier) x w) := by
  classical
  let W := fun i => Metric.ball (0 : E) (ρ i)
  let hW : ∀ i, IsOpen (W i) := fun _ => Metric.isOpen_ball
  let : ∀ i, Nonempty (Piece W i) := fun i => ⟨⟨0, Metric.mem_ball_self (hρ i)⟩⟩
  let : ∀ i, ChartedSpace E (Piece W i) :=
    fun i => (hW i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ i, IsManifold (𝓡 3) ∞ (Piece W i) :=
    fun i => (hW i).isOpenEmbedding_subtypeVal.isManifold_singleton
  let q : ∀ i, Piece W i → G.limit.sliceCarrier.carrier := fun i x => (Φ i x).val
  change ∀ F, _
  intro F hcoeff hpair hOld
  have hsub (i : Fin (N + 1)) : W i ⊆ (Φ i).source := by
    rw [hsource i]
    exact Metric.ball_subset_ball (hρR i).le
  obtain ⟨hq, _hderiv, _himage⟩ :=
    limitFinite_endpoint_chart_maps (fun _ => U) W hW Φ hsub
  have hmetric : ∀ t ∈ J, ∀ i l (x : Piece W i) (y : Piece W l), q i x = q l y →
      ∀ a b c e : E,
        mfderiv (𝓡 3) (𝓡 3) (q i) x a = mfderiv (𝓡 3) (𝓡 3) (q l) y c →
        mfderiv (𝓡 3) (𝓡 3) (q i) x b = mfderiv (𝓡 3) (𝓡 3) (q l) y e →
        ((F i).metric t).inner x a b = ((F l).metric t).inner y c e := by
    intro t ht
    exact limitFinite_endpoint_chart_pairing (fun _ => U) W hW Φ hsub
      (fun i z => B i (t - (-H.toReal + d / 4), z)) (hpair t ht)
      (fun i => (F i).metric t) (hcoeff t ht)
  let Fpart : ∀ i, RicciFlow 3 (terminalGermsOpenChartSource (q i) (hq i) V) J :=
    fun i => (F i).restrictToOpen (terminalGermsOpenChartSource (q i) (hq i) V)
  have hpartCover : ∀ y : V, ∃ i,
      ∃ x : terminalGermsOpenChartSource (q i) (hq i) V,
        terminalGermsOpenChartMap (q i) (hq i) V x = y := by
    intro y
    obtain ⟨i, z, hz, heq⟩ := mem_iUnion.mp (hcover (subset_closure y.property))
    have hx : q i ⟨z, hz⟩ ∈ V :=
      (congrArg (fun x => x ∈ V) heq).mpr y.property
    exact ⟨i, ⟨⟨z, hz⟩, hx⟩, Subtype.ext heq⟩
  have ht0 : -H.toReal ∈ J := ⟨by linarith, by linarith⟩
  obtain ⟨A, hA⟩ := limitFinite_endpoint_flow_descent Fpart ht0
    (fun i => terminalGermsOpenChartMap (q i) (hq i) V)
    (fun i => terminalGerms_openChartMap_localDiffeomorph (q i) (hq i) V)
    hpartCover (by
      intro t ht i l x y hxy a b c e ha hb
      exact terminalGerms_open_metric_compatibility (q i) (q l) (hq i) (hq l)
        ((F i).metric t) ((F l).metric t) (hmetric t ht i l) V x y hxy a b c e ha hb)
  refine ⟨A, ht0, ?_, ?_⟩
  · intro t ht i x hx v w
    exact terminalGerms_open_metric_readout (q i) (hq i) V ((F i).metric t)
      (A.metric t) (hA t ht i) x hx v w
  · intro t ht htOld y v w
    have hold : ∀ i (x : Piece W i) (a b : E), ((F i).metric t).inner x a b =
        (G.limit.flow.metric t).inner (q i x)
          (mfderiv (𝓡 3) (𝓡 3) (q i) x a) (mfderiv (𝓡 3) (𝓡 3) (q i) x b) :=
      limitFinite_endpoint_chart_old_metric (fun _ => U) W hW Φ hsub
        (G.limit.flow.metric t) (fun i z => B i (t - (-H.toReal + d / 4), z))
        (hOld t ht htOld) (fun i => (F i).metric t) (hcoeff t ht)
    obtain ⟨i, x, rfl⟩ := hpartCover y
    have hlocal := terminalGerms_openChartMap_localDiffeomorph (q i) (hq i) V
    let L := hlocal.mfderivToContinuousLinearEquiv (by simp) x
    let a := L.symm v
    let b := L.symm w
    have ha : mfderiv (𝓡 3) (𝓡 3) (terminalGermsOpenChartMap (q i) (hq i) V) x a = v :=
      L.apply_symm_apply v
    have hb : mfderiv (𝓡 3) (𝓡 3) (terminalGermsOpenChartMap (q i) (hq i) V) x b = w :=
      L.apply_symm_apply w
    have heq := (hA t ht i x a b).symm.trans
      (terminalGerms_open_terminal_metric (q i) (hq i) ((F i).metric t)
        (G.limit.flow.metric t) (hold i) V x a b)
    rw [ha, hb] at heq
    exact heq

end PoincareConjecture.M47
