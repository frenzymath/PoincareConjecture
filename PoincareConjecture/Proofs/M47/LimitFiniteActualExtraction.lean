import PoincareConjecture.Proofs.M47.LimitFiniteEndpointOriginalCover
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointExtraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance actualExtractionDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualExtractionDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance actualExtractionBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualExtractionBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance actualExtractionTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance actualExtractionCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance actualExtractionManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

local notation "U" => (fun j : ℕ =>
  TopologicalSpace.Opens.mk (G.exhaustion.space j) (G.exhaustion.space_open j))

set_option maxHeartbeats 1000000 in

theorem limitFinite_actual_endpoint_extraction (P : M47Predecessors.{u})
    (d K : ℕ → ℝ) (hd : ∀ j, 0 < d j) (hK : ∀ j, 0 < K j)
    (hc : ∀ j, -H.toReal + d j / 4 ∈ blowupBackwardInterval H)
    (A : ∀ j, ℕ → RicciFlow 3 (U j) (Icc (-(H.toReal + d j / 2)) 0))
    (hcandidates : ∀ j, ∀ᶠ k : ℕ in atTop,
      (∀ s ∈ Icc (-(H.toReal + d j / 2)) 0, ∀ x : U j,
        |((A j k).connection s).curvatureTensorNorm x| ≤ K j) ∧
      ∃ ht : -H.toReal + d j / 4 ∈ Icc (-G.exhaustion.time k) 0,
        ∀ (x : U j) (v w : TangentSpace (𝓡 3) x),
          ((A j k).metric (-H.toReal + d j / 4)).inner x v w =
            (G.embedding k).pullbackInner (-H.toReal + d j / 4) ht x.val
              (mfderiv (𝓡 3) (𝓡 3)
                (Subtype.val : U j → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3)
                (Subtype.val : U j → G.limit.sliceCarrier.carrier) x w)) :
    ∃ j : ℕ → ℕ, (∀ m, closure (G.exhaustion.space m) ⊆ G.exhaustion.space (j m)) ∧
      ∃ N : ℕ → ℕ, ∃ q : ∀ m, Fin (N m + 1) → closure (G.exhaustion.space m),
        ∃ R ρ : ∀ m, Fin (N m + 1) → ℝ,
          ∃ Φ : ∀ m, Fin (N m + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E (U (j m)) ∞,
            (∀ m i, 0 < ρ m i ∧ 2 * ρ m i < R m i ∧
              (Φ m i).source = Metric.ball 0 (R m i) ∧ (Φ m i 0).val = (q m i).val) ∧
            (∀ m, closure (G.exhaustion.space m) ⊆
              ⋃ i, (fun z : E => (Φ m i z).val) '' Metric.ball 0 (ρ m i)) ∧
            (∀ m i z, z ∈ Metric.ball 0 (R m i) →
              (Φ m i z).val = (extChartAt (𝓡 3) (q m i).val).symm
                ((extChartAt (𝓡 3) (q m i).val) (q m i).val + z)) ∧
            let Ω := fun m i =>
              Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) (ρ m i)
            let f := fun m i k (p : ℝ × E) =>
              ((A (j m) k).metric (p.1 + (-H.toReal + d (j m) / 4))).pullbackCoefficients
                (Φ m i) p.2
            ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ B : ∀ m, Fin (N m + 1) → ℝ × E → V,
              (∀ m i, ContDiffOn ℝ ∞ (B m i) (Ω m i)) ∧
              (∀ m i order C, IsCompact C → C ⊆ Ω m i → TendstoUniformlyOn
                (fun k => iteratedFDeriv ℝ order (f m i (σ k)))
                (iteratedFDeriv ℝ order (B m i)) atTop C) ∧
              (∀ m i p, p ∈ Ω m i →
                Tendsto (fun k => f m i (σ k) p) atTop (𝓝 (B m i p))) ∧
              (∀ m i p, p ∈ Ω m i → ∀ v w, B m i p v w = B m i p w v) ∧
              ∀ m i, ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧ ∀ p ∈ Ω m i, ∀ v : E,
                a * ‖v‖ ^ 2 ≤ B m i p v v ∧ B m i p v v ≤ b * ‖v‖ ^ 2 := by
  classical
  choose j hj N q R ρ Φ hdata hcover hmap hjets using
    fun m => limitFinite_original_endpoint_chart_cover G P d K hd hK hc m
  let label := terminalSourceCountableLabel N
  obtain ⟨σ, hσ, B, hB, hconv, hpoint, hsymm, hquad⟩ :=
    limitFinite_endpoint_row_extraction G (fun n => j (label n).1)
      (fun n => d (j (label n).1)) (fun n => K (j (label n).1))
      (fun n => R (label n).1 (label n).2) (fun n => ρ (label n).1 (label n).2)
      (fun n => hd (j (label n).1)) (fun n => hK (j (label n).1))
      (fun n => (hdata (label n).1 (label n).2).1)
      (fun n => (hdata (label n).1 (label n).2).2.1)
      (fun n => hc (j (label n).1)) (fun n => Φ (label n).1 (label n).2)
      (fun n => (hdata (label n).1 (label n).2).2.2.1)
      (fun n => hjets (label n).1 (label n).2)
      (fun n => A (j (label n).1)) (fun n => hcandidates (j (label n).1))
  have hdomain (m : ℕ) (i : Fin (N m + 1)) :
      Ioo (-((3 * d (j (label (Nat.pair m i.val)).1) / 4) / 2)) 0 ×ˢ
          Metric.ball (0 : E) (ρ (label (Nat.pair m i.val)).1 (label (Nat.pair m i.val)).2) =
        Ioo (-((3 * d (j m) / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) (ρ m i) :=
    congrArg (fun li : Σ m, Fin (N m + 1) =>
      Ioo (-((3 * d (j li.1) / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) (ρ li.1 li.2))
      (terminalSourceCountableLabel_pair N m i)
  refine ⟨j, hj, N, q, R, ρ, Φ, hdata, hcover, hmap, σ, hσ,
    (fun m i => B (Nat.pair m i.val)), ?_, ?_, ?_, ?_, ?_⟩
  · intro m i
    simpa only [hdomain m i] using hB (Nat.pair m i.val)
  · intro m i order C hC hCΩ
    have transport := congrArg (fun li : Σ m, Fin (N m + 1) =>
      C ⊆ Ioo (-((3 * d (j li.1) / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) (ρ li.1 li.2) →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ order (fun p : ℝ × E =>
          ((A (j li.1) (σ k)).metric (p.1 + (-H.toReal + d (j li.1) / 4))).pullbackCoefficients
            (Φ li.1 li.2) p.2)) (iteratedFDeriv ℝ order (B (Nat.pair m i.val))) atTop C)
      (terminalSourceCountableLabel_pair N m i)
    exact (transport.mp (hconv (Nat.pair m i.val) order C hC)) hCΩ
  · intro m i p hp
    have transport := congrArg (fun li : Σ m, Fin (N m + 1) =>
      p ∈ Ioo (-((3 * d (j li.1) / 4) / 2)) 0 ×ˢ Metric.ball (0 : E) (ρ li.1 li.2) →
        Tendsto (fun k =>
          ((A (j li.1) (σ k)).metric (p.1 + (-H.toReal + d (j li.1) / 4))).pullbackCoefficients
            (Φ li.1 li.2) p.2) atTop (𝓝 (B (Nat.pair m i.val) p)))
      (terminalSourceCountableLabel_pair N m i)
    exact (transport.mp (hpoint (Nat.pair m i.val) p)) hp
  · intro m i p hp v w
    have h := hsymm (Nat.pair m i.val) p
    simp only [hdomain m i] at h
    exact h hp v w
  · intro m i
    simpa only [hdomain m i] using hquad (Nat.pair m i.val)

end PoincareConjecture.M47
