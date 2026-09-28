import PoincareConjecture.Proofs.M47.LimitFiniteOriginalEllipticity
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSmoothExtraction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteEndpointExtractDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointExtractDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteEndpointExtractBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointExtractBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteEndpointExtractTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteEndpointExtractCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteEndpointExtractManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

variable (j : ℕ → ℕ)

local notation "U" => (fun i : ℕ =>
  TopologicalSpace.Opens.mk (G.exhaustion.space (j i)) (G.exhaustion.space_open (j i)))



theorem limitFinite_endpoint_row_extraction
    (d K R ρ : ℕ → ℝ) (hd : ∀ i, 0 < d i) (hK : ∀ i, 0 < K i)
    (hρ : ∀ i, 0 < ρ i) (hρR : ∀ i, 2 * ρ i < R i)
    (hc : ∀ i, -H.toReal + d i / 4 ∈ blowupBackwardInterval H)
    (Φ : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) E (U i) ∞)
    (hsource : ∀ i, (Φ i).source = Metric.ball 0 (R i))
    (hjets : ∀ i m, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ ht : -H.toReal + d i / 4 ∈ Icc (-G.exhaustion.time k) 0,
        ∀ A : RicciFlow 3 (U i) (Icc (-(H.toReal + d i / 2)) 0),
          (∀ s ∈ Icc (-(H.toReal + d i / 2)) 0, ∀ x : U i,
            |(A.connection s).curvatureTensorNorm x| ≤ K i) →
          (∀ (x : U i) (v w : TangentSpace (𝓡 3) x),
            (A.metric (-H.toReal + d i / 4)).inner x v w =
              (G.embedding k).pullbackInner (-H.toReal + d i / 4) ht x.val
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U i → G.limit.sliceCarrier.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U i → G.limit.sliceCarrier.carrier) x w)) →
          ∀ s ∈ Ioo (-((3 * d i / 4) / 2)) 0, ∀ z ∈ Metric.closedBall 0 (ρ i),
            ‖iteratedFDeriv ℝ m (fun p : ℝ × E =>
              (A.metric (p.1 + (-H.toReal + d i / 4))).pullbackCoefficients
                (Φ i) p.2) (s, z)‖ ≤ C)
    (A : ∀ i, ℕ → RicciFlow 3 (U i) (Icc (-(H.toReal + d i / 2)) 0))
    (hcandidates : ∀ i, ∀ᶠ k : ℕ in atTop,
      (∀ s ∈ Icc (-(H.toReal + d i / 2)) 0, ∀ x : U i,
        |((A i k).connection s).curvatureTensorNorm x| ≤ K i) ∧
      ∃ ht : -H.toReal + d i / 4 ∈ Icc (-G.exhaustion.time k) 0,
        ∀ (x : U i) (v w : TangentSpace (𝓡 3) x),
          ((A i k).metric (-H.toReal + d i / 4)).inner x v w =
            (G.embedding k).pullbackInner (-H.toReal + d i / 4) ht x.val
              (mfderiv (𝓡 3) (𝓡 3)
                (Subtype.val : U i → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3)
                (Subtype.val : U i → G.limit.sliceCarrier.carrier) x w)) :
    let Ω := fun i => Ioo (-((3 * d i / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) (ρ i)
    let f := fun i k (p : ℝ × E) =>
      ((A i k).metric (p.1 + (-H.toReal + d i / 4))).pullbackCoefficients (Φ i) p.2
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ B : ℕ → ℝ × E → V,
      (∀ i, ContDiffOn ℝ ∞ (B i) (Ω i)) ∧
      (∀ i m C, IsCompact C → C ⊆ Ω i → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f i (σ k)))
        (iteratedFDeriv ℝ m (B i)) atTop C) ∧
      (∀ i p, p ∈ Ω i → Tendsto (fun k => f i (σ k) p) atTop (𝓝 (B i p))) ∧
      (∀ i p, p ∈ Ω i → ∀ v w, B i p v w = B i p w v) ∧
      ∀ i, ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ p ∈ Ω i, ∀ v : E,
        a * ‖v‖ ^ 2 ≤ B i p v v ∧ B i p v v ≤ b * ‖v‖ ^ 2 := by
  classical
  let Ω := fun i => Ioo (-((3 * d i / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) (ρ i)
  let f := fun i k (p : ℝ × E) =>
    ((A i k).metric (p.1 + (-H.toReal + d i / 4))).pullbackCoefficients (Φ i) p.2
  have hsmooth : ∀ i k, ContDiffOn ℝ ∞ (f i k) (Ω i) := by
    intro i k
    have hPhi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Φ i) (Metric.ball 0 (R i)) := by
      simpa only [hsource i] using (Φ i).contMDiffOn
    apply (M44.contDiffOn_pullbackCoefficients_within (A i k) Metric.isOpen_ball hPhi).comp
      ((contDiffOn_fst.add contDiffOn_const).prodMk contDiffOn_snd)
    intro p hp
    refine ⟨⟨?_, ?_⟩, Metric.ball_subset_ball (by linarith [hρR i, hρ i]) hp.2⟩
    · linarith [hp.1.1, hd i]
    · linarith [hp.1.2, (hc i).1]
  have hbound : ∀ i C, IsCompact C → C ⊆ Ω i → ∀ m : ℕ, ∃ D : ℝ,
      ∀ᶠ k in atTop, ∀ p ∈ C, ‖iteratedFDeriv ℝ m (f i k) p‖ ≤ D := by
    intro i C _hC hCΩ m
    obtain ⟨D, _hD, htail⟩ := hjets i m
    refine ⟨D, ?_⟩
    filter_upwards [htail, hcandidates i] with k hk hA p hp
    obtain ⟨ht, hread⟩ := hA.2
    exact hk ht (A i k) hA.1 hread p.1 (hCΩ hp).1 p.2
      (Metric.ball_subset_closedBall (hCΩ hp).2)
  obtain ⟨σ, hσ, B, hB, hconv⟩ := terminalCommonInterval_smooth_row_extraction
    (fun _ => isOpen_Ioo.prod Metric.isOpen_ball) f hsmooth hbound
  have hpoint : ∀ i p, p ∈ Ω i →
      Tendsto (fun k => f i (σ k) p) atTop (𝓝 (B i p)) := by
    intro i p hp
    have hzero := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × E)).comp_tendstoUniformlyOn
        (hconv i 0 {p} isCompact_singleton (singleton_subset_iff.mpr hp))
    have h := hzero.tendsto_at (mem_singleton p)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using h
  have heval (i : ℕ) (p : ℝ × E) (hp : p ∈ Ω i) (v w : E) :
      Tendsto (fun k => f i (σ k) p v w) atTop (𝓝 (B i p v w)) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous.tendsto _).comp
        (hpoint i p hp))
  refine ⟨σ, hσ, B, hB, hconv, hpoint, ?_, ?_⟩
  · intro i p hp v w
    have hsymm : (fun k => f i (σ k) p v w) = fun k => f i (σ k) p w v := by
      funext k
      exact ((A i (σ k)).metric (p.1 + (-H.toReal + d i / 4))).symm _ _ _
    exact tendsto_nhds_unique (heval i p hp v w)
      (hsymm ▸ heval i p hp w v)
  · intro i
    obtain ⟨a, b, ha, hb, hquad⟩ := limitFinite_original_source_ellipticity G
      (hd i) (hK i) (hρ i) (hρR i) (hc i) (j i) (Φ i) (hsource i)
    refine ⟨a, b, ha, hb, ?_⟩
    intro p hp v
    have htail : ∀ᶠ k in atTop,
        a * ‖v‖ ^ 2 ≤ f i k p v v ∧ f i k p v v ≤ b * ‖v‖ ^ 2 := by
      filter_upwards [hquad, hcandidates i] with k hk hA
      obtain ⟨ht, hread⟩ := hA.2
      apply hk ht (A i k) hA.1 hread p.1
        ⟨by linarith [hp.1.1, hd i], hp.1.2.le⟩ p.2
        ((Metric.closedBall_subset_closedBall (by linarith [hρ i]))
          (Metric.ball_subset_closedBall hp.2)) v
    have htail' := hσ.tendsto_atTop.eventually htail
    exact ⟨ge_of_tendsto (heval i p hp v v) (htail'.mono fun _ h => h.1),
      le_of_tendsto (heval i p hp v v) (htail'.mono fun _ h => h.2)⟩

end PoincareConjecture.M47
