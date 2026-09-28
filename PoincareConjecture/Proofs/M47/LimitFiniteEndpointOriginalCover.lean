import PoincareConjecture.Proofs.M47.LimitFiniteEndpointChartCover
import PoincareConjecture.Proofs.M47.TerminalSourceCountableLabels









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteEndpointCoverDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointCoverDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteEndpointCoverBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointCoverBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteEndpointCoverTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteEndpointCoverCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteEndpointCoverManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitFinite_original_endpoint_chart_cover (P : M47Predecessors.{u})
    (d K : ℕ → ℝ) (hd : ∀ j, 0 < d j) (hK : ∀ j, 0 < K j)
    (hc : ∀ j, -H.toReal + d j / 4 ∈ blowupBackwardInterval H) (m : ℕ) :
    ∃ j : ℕ, closure (G.exhaustion.space m) ⊆ G.exhaustion.space j ∧
      let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
        ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
      ∃ N : ℕ, ∃ q : Fin (N + 1) → closure (G.exhaustion.space m),
        ∃ R ρ : Fin (N + 1) → ℝ,
          ∃ Φ : Fin (N + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
            (∀ i, 0 < ρ i ∧ 2 * ρ i < R i ∧
              (Φ i).source = Metric.ball 0 (R i) ∧ (Φ i 0).val = (q i).val) ∧
            closure (G.exhaustion.space m) ⊆
              ⋃ i, (fun z : E => (Φ i z).val) '' Metric.ball 0 (ρ i) ∧
            (∀ i z, z ∈ Metric.ball 0 (R i) →
              (Φ i z).val = (extChartAt (𝓡 3) (q i).val).symm
                ((extChartAt (𝓡 3) (q i).val) (q i).val + z)) ∧
            ∀ i order, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
              ∀ ht : -H.toReal + d j / 4 ∈ Icc (-G.exhaustion.time k) 0,
                ∀ A : RicciFlow 3 U (Icc (-(H.toReal + d j / 2)) 0),
                  (∀ s ∈ Icc (-(H.toReal + d j / 2)) 0, ∀ x : U,
                    |(A.connection s).curvatureTensorNorm x| ≤ K j) →
                  (∀ (x : U) (v w : TangentSpace (𝓡 3) x),
                    (A.metric (-H.toReal + d j / 4)).inner x v w =
                      (G.embedding k).pullbackInner (-H.toReal + d j / 4) ht x.val
                        (mfderiv (𝓡 3) (𝓡 3)
                          (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                        (mfderiv (𝓡 3) (𝓡 3)
                          (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)) →
                  ∀ s ∈ Ioo (-((3 * d j / 4) / 2)) 0,
                    ∀ z ∈ Metric.closedBall 0 (ρ i),
                      ‖iteratedFDeriv ℝ order (fun p : ℝ × E =>
                        (A.metric (p.1 + (-H.toReal + d j / 4))).pullbackCoefficients
                          (Φ i) p.2) (s, z)‖ ≤ C := by
  classical
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (G.exhaustion.space_compactClosure m)
  let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
  let Good := fun (q : closure (G.exhaustion.space m)) (R ρ : ℝ)
      (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞) =>
    (∀ z ∈ Metric.ball 0 R, (Φ z).val = (extChartAt (𝓡 3) q.val).symm
      ((extChartAt (𝓡 3) q.val) q.val + z)) ∧
    ∀ order, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ ht : -H.toReal + d j / 4 ∈ Icc (-G.exhaustion.time k) 0,
        ∀ A : RicciFlow 3 U (Icc (-(H.toReal + d j / 2)) 0),
          (∀ s ∈ Icc (-(H.toReal + d j / 2)) 0, ∀ x : U,
            |(A.connection s).curvatureTensorNorm x| ≤ K j) →
          (∀ (x : U) (v w : TangentSpace (𝓡 3) x),
            (A.metric (-H.toReal + d j / 4)).inner x v w =
              (G.embedding k).pullbackInner (-H.toReal + d j / 4) ht x.val
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3)
                  (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)) →
          ∀ s ∈ Ioo (-((3 * d j / 4) / 2)) 0, ∀ z ∈ Metric.closedBall 0 ρ,
            ‖iteratedFDeriv ℝ order (fun p : ℝ × E =>
              (A.metric (p.1 + (-H.toReal + d j / 4))).pullbackCoefficients Φ p.2)
                (s, z)‖ ≤ C
  have hcharts : ∀ q : closure (G.exhaustion.space m),
      ∃ R ρ : ℝ, 0 < ρ ∧ 2 * ρ < R ∧
        ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
          Φ.source = Metric.ball 0 R ∧ (Φ 0).val = q.val ∧ Good q R ρ Φ := by
    intro q
    obtain ⟨_ht, _hclock, R, ρ, hρ, hρR, Φ, hsource, hzero, hmap, hjets⟩ :=
      limitFinite_exists_original_source_jets G P (hd j) (hK j) (hc j) j q.val
        (hj q.property)
    exact ⟨R, ρ, hρ, hρR, Φ, hsource, congrArg Subtype.val hzero, hmap, hjets⟩
  obtain ⟨N, q, R, ρ, Φ, hdata, hcover⟩ := limitFinite_compact_chart_cover U
    (G.exhaustion.space_compactClosure m)
    ⟨G.limit.base, subset_closure (G.exhaustion.base_mem m)⟩ Good hcharts
  refine ⟨j, hj, N, q, R, ρ, Φ, ?_, hcover, ?_, ?_⟩
  · intro i
    exact ⟨(hdata i).1, (hdata i).2.1, (hdata i).2.2.1, (hdata i).2.2.2.1⟩
  · intro i
    exact (hdata i).2.2.2.2.1
  · intro i
    exact (hdata i).2.2.2.2.2



theorem limitFinite_endpoint_countable_chart_cover
    (j N : ℕ → ℕ) (ρ : ∀ m, Fin (N m + 1) → ℝ)
    (Φ : ∀ m, Fin (N m + 1) → PartialDiffeomorph (𝓡 3) (𝓡 3) E
      (⟨G.exhaustion.space (j m), G.exhaustion.space_open (j m)⟩ :
        TopologicalSpace.Opens G.limit.sliceCarrier.carrier) ∞)
    (hcover : ∀ m, closure (G.exhaustion.space m) ⊆
      ⋃ i, (fun z : E => (Φ m i z).val) '' Metric.ball 0 (ρ m i)) :
    ∀ x : G.limit.sliceCarrier.carrier, ∃ n : ℕ, ∃ z : E,
      z ∈ Metric.ball 0 (ρ (terminalSourceCountableLabel N n).1
        (terminalSourceCountableLabel N n).2) ∧
      (Φ (terminalSourceCountableLabel N n).1
        (terminalSourceCountableLabel N n).2 z).val = x := by
  intro x
  have hx : x ∈ ⋃ m, G.exhaustion.space m := by
    rw [G.exhaustion.space_covers]
    exact mem_univ x
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover m (subset_closure hm))
  obtain ⟨z, hz, heq⟩ := hi
  obtain ⟨n, hn⟩ := terminalSourceCountableLabel_surjective N ⟨m, i⟩
  refine ⟨n, z, ?_⟩
  exact (congrArg (fun p : Σ m, Fin (N m + 1) =>
    z ∈ Metric.ball 0 (ρ p.1 p.2) ∧ (Φ p.1 p.2 z).val = x) hn).mpr ⟨hz, heq⟩

end PoincareConjecture.M47
