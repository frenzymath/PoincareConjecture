import PoincareConjecture.Proofs.M47.LimitFiniteEndpointGermSign
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointStageFlow
import PoincareConjecture.Proofs.M47.TerminalGermsExhaustionOperator
import PoincareConjecture.Proofs.M47.TerminalCurvatureNullLine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance endpointSignedDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointSignedDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance endpointSignedBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointSignedBilinSpace :
    NormedSpace ℝ Bilin := ContinuousLinearMap.toNormedSpace

theorem limitFinite_endpoint_signed_stage
    {N : ℕ} {P : Fin (N + 1) → Type*} {M : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace M]
    [∀ i, ChartedSpace E (P i)] [ChartedSpace E M]
    [∀ i, IsManifold (𝓡 3) ∞ (P i)] [IsManifold (𝓡 3) ∞ M]
    {T d : ℝ} (hd : 0 < d)
    (F : ∀ i, RicciFlow 3 (P i) (Ioo (-T - d / 8) (-T + d / 4)))
    (q : ∀ i, P i → M) (hq : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q i))
    (U : TopologicalSpace.Opens M) (hcover : ∀ y ∈ U, ∃ i x, q i x = y)
    (A : RicciFlow 3 U (Ioo (-T - d / 8) (-T + d / 4)))
    (hread : ∀ t ∈ Ioo (-T - d / 8) (-T + d / 4),
      ∀ i (x : P i) (hx : q i x ∈ U) (v w : TangentSpace (𝓡 3) x),
        ((F i).metric t).inner x v w = (A.metric t).inner ⟨q i x, hx⟩
          (mfderiv (𝓡 3) (𝓡 3) (q i) x v) (mfderiv (𝓡 3) (𝓡 3) (q i) x w))
    (hoperator : ∀ i t, t ∈ Ioo (-T - d / 8) (-T + d / 4) → ∀ x,
      ((F i).connection t).NonnegativeCurvatureOperator x) :
    ∃ L : RicciFlow 3 U (Icc (-(d / 32)) 0),
      (∀ s, L.metric s = A.metric (s - T)) ∧
      ∀ s ∈ Icc (-(d / 32)) 0, ∀ x,
        (L.connection s).NonnegativeCurvatureOperator x := by
  classical
  have hmapChart : (fun s : ℝ => s + -T) '' Icc (-(d / 16)) 0 ⊆
      Ioo (-T - d / 8) (-T + d / 4) := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  have hneChart : (Icc (-(d / 16)) (0 : ℝ)).Nontrivial :=
    ⟨-(d / 16), ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
  let Fc := fun i => (F i).translate (-T) hmapChart ordConnected_Icc hneChart
  have hmap : (fun s : ℝ => s + -T) '' Icc (-(d / 32)) 0 ⊆
      Ioo (-T - d / 8) (-T + d / 4) := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  have hne : (Icc (-(d / 32)) (0 : ℝ)).Nontrivial :=
    ⟨-(d / 32), ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
  let L := A.translate (-T) hmap ordConnected_Icc hne
  refine ⟨L, fun s => ?_, ?_⟩
  · rfl
  · apply terminalGerms_descended_operator (fun _ => d / 16) Fc q hq U Finset.univ
      (fun y hy => by
        obtain ⟨i, x, hx⟩ := hcover y hy
        exact ⟨i, Finset.mem_univ i, x, hx⟩)
      (fun _ _ => by linarith) L
    · intro s hs i _hsi x hx v w
      exact hread (s + -T) (hmap ⟨s, hs, rfl⟩) i x hx v w
    · intro i s hs x
      exact hoperator i (s + -T) (hmapChart ⟨s, hs, rfl⟩) x

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance endpointSignedTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance endpointSignedCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance endpointSignedManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

local notation "U" => (fun m : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space m) (G.exhaustion.space_open m))

theorem limitFinite_endpoint_original_signed_germs
    (Fraw : ℕ → SurgeryFlowData.{u})
    (hPinched : ∀ k, SurgeryFlowPinched (Fraw k))
    (base Q : ℕ → ℝ) (hQ : Tendsto Q atTop atTop)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (j N : ℕ → ℕ)
    (d K : ℕ → ℝ) (hd : ∀ m, 0 < d m) (hK : ∀ m, 0 ≤ K m)
    (hc : ∀ m, -H.toReal + d m / 4 ≤ 0)
    (Aseq : ∀ m, ℕ → RicciFlow 3 (U (j m)) (Icc (-(H.toReal + d m / 2)) 0))
    (hphysical : ∀ m, ∀ᶠ k in atTop, ∃ b, ∃ hb : b ≤ -(H.toReal + d m / 2),
      ∃ E0 : SurgeryFlowCylinder (Fraw (G.subsequence k)) G.limit.sliceCarrier
        (base (G.subsequence k)) (Q (G.subsequence k)) (Icc b 0) (U (j m)),
        (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U (j m),
          |((Fraw (G.subsequence k)).connection
            (base (G.subsequence k) + s / Q (G.subsequence k))).curvatureTensorNorm
              (E0.forward s hs x)| ≤ K m * Q (G.subsequence k)) ∧
        (∀ s (hs : s ∈ Icc (-(H.toReal + d m / 2)) 0) (x : U (j m)),
          ∀ v w : TangentSpace (𝓡 3) x,
            ((Aseq m k).metric s).inner x v w = E0.pullbackInner s
              ⟨hb.trans hs.1, hs.2⟩ x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x w)))
    (R ρ : ∀ m, Fin (N m + 1) → ℝ)
    (hρ : ∀ m i, 0 < ρ m i) (hρR : ∀ m i, ρ m i < R m i)
    (Φ : ∀ m, Fin (N m + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E (U (j m)) ∞)
    (hsource : ∀ m i, (Φ m i).source = Metric.ball 0 (R m i))
    (hcover : ∀ m, closure (G.exhaustion.space m) ⊆
      ⋃ i, (fun z : E => (Φ m i z).val) '' Metric.ball 0 (ρ m i))
    (B : ∀ m, Fin (N m + 1) → ℝ × E → Bilin)
    (hjets : ∀ m i r C, IsCompact C →
      C ⊆ Ioo (-((3 * d m / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i) → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((Aseq m (σ k)).metric (p.1 + (-H.toReal + d m / 4))).pullbackCoefficients
            (Φ m i) p.2)) (iteratedFDeriv ℝ r (B m i)) atTop C) :
    let W := fun p : Σ m, Fin (N m + 1) => Metric.ball (0 : E) (ρ p.1 p.2)
    let hW : ∀ p, IsOpen (W p) := fun _ => Metric.isOpen_ball
    letI : ∀ p, Nonempty (Piece W p) := fun p => ⟨⟨0, Metric.mem_ball_self (hρ p.1 p.2)⟩⟩
    letI : ∀ p, ChartedSpace E (Piece W p) :=
      fun p => (hW p).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI : ∀ p, IsManifold (𝓡 3) ∞ (Piece W p) :=
      fun p => (hW p).isOpenEmbedding_subtypeVal.isManifold_singleton
    let q : ∀ m i, Piece W ⟨m, i⟩ → G.limit.sliceCarrier.carrier :=
      fun m i x => (Φ m i x).val
    ∀ F : ∀ m i, RicciFlow 3 (Piece W ⟨m, i⟩)
        (Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)),
      (∀ m t, t ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) →
        ∀ i (x : Piece W ⟨m, i⟩) (v w : E),
          ((F m i).metric t).inner x v w = B m i (t - (-H.toReal + d m / 4), x) v w) →
      ∀ A : ∀ m, RicciFlow 3 (U m)
          (Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)),
        (∀ m t, t ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) →
          ∀ i (x : Piece W ⟨m, i⟩) (hx : q m i x ∈ U m) (v w : E),
            ((F m i).metric t).inner x v w = ((A m).metric t).inner ⟨q m i x, hx⟩
              (mfderiv (𝓡 3) (𝓡 3) (q m i) x v)
              (mfderiv (𝓡 3) (𝓡 3) (q m i) x w)) →
        ∀ gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier,
          (∀ m (x : U m) (v w : E), ((A m).metric (-H.toReal)).inner x v w =
            gE.inner x.val v w) →
          (∀ m, ConnectedSpace (U m)) ∧
            (∀ x y z : G.limit.sliceCarrier.carrier, ∃ m,
              x ∈ U m ∧ y ∈ U m ∧ z ∈ U m) ∧
            ∃ L : ∀ m, RicciFlow 3 (U m) (Icc (-(d m / 32)) 0),
              (∀ m, 0 < d m / 32) ∧
              (∀ m s, (L m).metric s = (A m).metric (s - H.toReal)) ∧
              (∀ m (x : U m) (v w : E),
                ((L m).metric 0).inner x v w = gE.inner x.val v w) ∧
              ∀ m s, s ∈ Icc (-(d m / 32)) 0 → ∀ x,
                ((L m).connection s).NonnegativeCurvatureOperator x := by
  classical
  let W := fun p : Σ m, Fin (N m + 1) => Metric.ball (0 : E) (ρ p.1 p.2)
  let hW : ∀ p, IsOpen (W p) := fun _ => Metric.isOpen_ball
  let : ∀ p, Nonempty (Piece W p) := fun p => ⟨⟨0, Metric.mem_ball_self (hρ p.1 p.2)⟩⟩
  let : ∀ p, ChartedSpace E (Piece W p) :=
    fun p => (hW p).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ p, IsManifold (𝓡 3) ∞ (Piece W p) :=
    fun p => (hW p).isOpenEmbedding_subtypeVal.isManifold_singleton
  let q : ∀ m i, Piece W ⟨m, i⟩ → G.limit.sliceCarrier.carrier :=
    fun m i x => (Φ m i x).val
  dsimp only
  intro F hcoeff A hread gE hterminal
  have hlower (m : ℕ) : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in atTop,
      ∀ t ∈ Icc (-(H.toReal + d m / 2)) 0, ∀ (x : U (j m))
        (v w : TangentSpace (𝓡 3) x),
          -eta ≤ ((Aseq m (σ k)).connection t).sectionalCurvature x v w := by
    exact limitFinite_eventually_preserved_source_sectional Fraw hPinched
      (fun k => G.subsequence (σ k)) base Q (U (j m)) (hK m)
      (fun k => Aseq m (σ k)) (hσ.tendsto_atTop.eventually (hphysical m))
      ((hQ.comp G.subsequence_strictMono.tendsto_atTop).comp hσ.tendsto_atTop)
  have hchart (m : ℕ) (i : Fin (N m + 1)) :
      ∀ t ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4), ∀ x,
        ((F m i).connection t).NonnegativeCurvatureOperator x := by
    exact limitFinite_endpoint_chart_operator (hd m) (hc m) (hρ m i) (hρR m i)
      (fun k => Aseq m (σ k)) (Φ m i) (hsource m i) (B m i) (hjets m i)
      (hlower m) (F m i) (fun t ht => hcoeff m t ht i)
  have hq (m : ℕ) : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q m i) := by
    have hsub (i : Fin (N m + 1)) : W ⟨m, i⟩ ⊆ (Φ m i).source := by
      rw [hsource m i]
      exact Metric.ball_subset_ball (hρR m i).le
    exact (limitFinite_endpoint_chart_maps (fun _ => U (j m))
      (fun i => W ⟨m, i⟩) (fun i => hW ⟨m, i⟩) (Φ m) hsub).1
  have hstage (m : ℕ) : ∃ L : RicciFlow 3 (U m) (Icc (-(d m / 32)) 0),
      (∀ s, L.metric s = (A m).metric (s - H.toReal)) ∧
      ∀ s ∈ Icc (-(d m / 32)) 0, ∀ x,
        (L.connection s).NonnegativeCurvatureOperator x := by
    apply limitFinite_endpoint_signed_stage (hd m) (F m) (q m) (hq m) (U m) ?_
      (A m) (hread m) (hchart m)
    intro y hy
    obtain ⟨i, z, hz, heq⟩ := mem_iUnion.mp (hcover m (subset_closure hy))
    exact ⟨i, ⟨z, hz⟩, heq⟩
  choose L hmetric hoperator using hstage
  refine ⟨fun m => isConnected_iff_connectedSpace.mp (G.exhaustion.space_connected m),
    terminalCurvature_exhaustion_triple U G.exhaustion.space_increasing
      G.exhaustion.space_covers,
    L, fun m => div_pos (hd m) (by norm_num), hmetric, ?_, hoperator⟩
  intro m x v w
  rw [hmetric m 0]
  simpa only [zero_sub] using hterminal m x v w

end PoincareConjecture.M47
