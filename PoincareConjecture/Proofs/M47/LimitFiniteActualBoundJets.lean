import PoincareConjecture.Proofs.M47.LimitFiniteActualBoundMaps
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointPhysicalJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance actualJetsDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualJetsDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance actualJetsBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance actualJetsBilinSpace :
    NormedSpace ℝ Bilin := ContinuousLinearMap.toNormedSpace

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance actualJetsTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance actualJetsCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance actualJetsManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

local notation "U" => (fun j : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j))

theorem limitFinite_actual_endpoint_jets
    (F : ℕ → SurgeryFlowData.{u}) (base Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    (j N : ℕ → ℕ) (d : ℕ → ℝ) (hd : ∀ m, 0 < d m)
    (hc : ∀ m, -H.toReal + d m / 4 ≤ 0)
    (A : ∀ m, ℕ → RicciFlow 3 (U (j m)) (Icc (-(H.toReal + d m / 2)) 0))
    (σ η : ℕ → ℕ) (hη : StrictMono η)
    (ψ : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.sliceCarrier.carrier
      ((F (G.subsequence (σ (η k)))).slice
        (base (G.subsequence (σ (η k))) + -H.toReal / Q (G.subsequence (σ (η k))))).carrier ∞)
    (hphysical : ∀ m, ∀ᶠ k in atTop,
      ∃ b, ∃ ht : -H.toReal ∈ Icc b 0,
        ∃ e : SurgeryFlowCylinder (F (G.subsequence (σ (η k)))) G.limit.sliceCarrier
            (base (G.subsequence (σ (η k)))) (Q (G.subsequence (σ (η k))))
            (Icc b 0) (U (j m)),
          EqOn (ψ k) (e.forward (-H.toReal) ht) (U (j m)) ∧
          ∀ (x : U (j m)) (v w : E), ((A m (σ (η k))).metric (-H.toReal)).inner x v w =
            e.pullbackInner (-H.toReal) ht x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (j m) → G.limit.sliceCarrier.carrier) x w))
    (R ρ : ∀ m, Fin (N m + 1) → ℝ) (hρR : ∀ m i, ρ m i < R m i)
    (Φ : ∀ m, Fin (N m + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E (U (j m)) ∞)
    (hsource : ∀ m i, (Φ m i).source = Metric.ball 0 (R m i))
    (hcover : ∀ m, closure (G.exhaustion.space m) ⊆
      ⋃ i, (fun z : E => (Φ m i z).val) '' Metric.ball 0 (ρ m i))
    (B : ∀ m, Fin (N m + 1) → ℝ × E → Bilin)
    (hB : ∀ m i, ContDiffOn ℝ ∞ (B m i)
      (Ioo (-((3 * d m / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i)))
    (hjets : ∀ m i r C, IsCompact C →
      C ⊆ Ioo (-((3 * d m / 4) / 2)) 0 ×ˢ Metric.ball 0 (ρ m i) →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((A m (σ k)).metric (p.1 + (-H.toReal + d m / 4))).pullbackCoefficients (Φ m i) p.2))
          (iteratedFDeriv ℝ r (B m i)) atTop C)
    (gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier)
    (hendpoint : ∀ m i, EqOn (fun z => B m i (-d m / 4, z))
      (gE.pullbackCoefficients (fun z : E => (Φ m i z).val)) (Metric.ball 0 (ρ m i))) :
    ∃ c : (Σ m, Fin (N m + 1)) →
        PartialDiffeomorph (𝓡 3) (𝓡 3) G.limit.sliceCarrier.carrier E ∞,
      (∀ p, ((c p).symm : E → G.limit.sliceCarrier.carrier) =
        fun z => (Φ p.1 p.2 z).val) ∧
      (∀ p, (c p).source = (fun z : E => (Φ p.1 p.2 z).val) '' Metric.ball 0 (ρ p.1 p.2) ∧
        (c p).target = Metric.ball 0 (ρ p.1 p.2)) ∧
      (∀ x, ∃ p, x ∈ (c p).source) ∧
      ∀ p r C, IsCompact C → C ⊆ (c p).target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r
          ((rescaledMetric ((F (G.subsequence (σ (η k)))).metric
              (base (G.subsequence (σ (η k))) + -H.toReal / Q (G.subsequence (σ (η k)))))
              (Q (G.subsequence (σ (η k)))) (hQ (G.subsequence (σ (η k))))).pullbackCoefficients
            (ψ k ∘ (c p).symm)))
        (iteratedFDeriv ℝ r (gE.pullbackCoefficients (c p).symm)) atTop C := by
  classical
  let Wb := fun p : Σ m, Fin (N m + 1) => Metric.ball (0 : E) (ρ p.1 p.2)
  have hsub (p : Σ m, Fin (N m + 1)) : Wb p ⊆ (Φ p.1 p.2).source := by
    rw [hsource p.1 p.2]
    exact Metric.ball_subset_ball (hρR p.1 p.2).le
  have hcoverAll (x : G.limit.sliceCarrier.carrier) :
      ∃ p : Σ m, Fin (N m + 1), x ∈ (fun z : E => (Φ p.1 p.2 z).val) '' Wb p := by
    have hx : x ∈ ⋃ m, G.exhaustion.space m := by
      rw [G.exhaustion.space_covers]
      exact mem_univ _
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover m (subset_closure hm))
    exact ⟨⟨m, i⟩, hi⟩
  obtain ⟨c, hinverse, hchart, hcoverC⟩ := limitFinite_endpoint_original_charts
    (fun p : Σ m, Fin (N m + 1) => U (j p.1)) Wb
    (fun _ => Metric.isOpen_ball) (fun p => Φ p.1 p.2) hsub hcoverAll
  refine ⟨c, hinverse, hchart, hcoverC, ?_⟩
  intro p r C hC hCW
  have hball : C ⊆ Metric.ball 0 (ρ p.1 p.2) := by
    simpa only [(hchart p).2] using hCW
  have h := limitFinite_endpoint_physical_jet_readout
    (fun k => F (G.subsequence (σ (η k))))
    (fun k => base (G.subsequence (σ (η k)))) (fun k => Q (G.subsequence (σ (η k))))
    (fun k => hQ (G.subsequence (σ (η k)))) (U (j p.1))
    (hd p.1) (hc p.1) (hρR p.1 p.2) (A p.1) (Φ p.1 p.2) (hsource p.1 p.2)
    σ η hη ψ (hphysical p.1) (B p.1 p.2) (hB p.1 p.2) (hjets p.1 p.2)
    gE (hendpoint p.1 p.2) r C hC hball
  simpa only [hinverse p] using h

end PoincareConjecture.M47
