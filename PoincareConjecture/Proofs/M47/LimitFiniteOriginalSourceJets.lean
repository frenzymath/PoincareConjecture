import PoincareConjecture.Proofs.M47.LimitFiniteAnchorJets
import PoincareConjecture.Proofs.M47.LimitFiniteChartMixed
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteOriginalSourceDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteOriginalSourceDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteOriginalSourceBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteOriginalSourceBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteOriginalSourceTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteOriginalSourceCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteOriginalSourceManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitFinite_exists_original_source_jets (P : M47Predecessors.{u})
    {d K : ℝ} (hd : 0 < d) (hK : 0 < K)
    (hc : -H.toReal + d / 4 ∈ blowupBackwardInterval H) (j : ℕ)
    (q : G.limit.sliceCarrier.carrier) (hq : q ∈ G.exhaustion.space j) :
    let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
      ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩;
    -d / 4 ∈ Ioo (-((3 * d / 4) / 2)) 0 ∧
      -d / 4 + (-H.toReal + d / 4) = -H.toReal ∧
      ∃ R ρ : ℝ, 0 < ρ ∧ 2 * ρ < R ∧
        ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
          Φ.source = Metric.ball 0 R ∧ Φ 0 = ⟨q, hq⟩ ∧
          (∀ z ∈ Metric.ball 0 R,
            (Φ z).val = (extChartAt (𝓡 3) q).symm ((extChartAt (𝓡 3) q) q + z)) ∧
          ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
            ∀ ht : -H.toReal + d / 4 ∈ Icc (-G.exhaustion.time k) 0,
              ∀ A : RicciFlow 3 U (Icc (-(H.toReal + d / 2)) 0),
                (∀ s ∈ Icc (-(H.toReal + d / 2)) 0, ∀ x : U,
                  |(A.connection s).curvatureTensorNorm x| ≤ K) →
                (∀ (x : U) (v w : TangentSpace (𝓡 3) x),
                  (A.metric (-H.toReal + d / 4)).inner x v w =
                    (G.embedding k).pullbackInner (-H.toReal + d / 4) ht x.val
                      (mfderiv (𝓡 3) (𝓡 3)
                        (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
                      (mfderiv (𝓡 3) (𝓡 3)
                        (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)) →
                ∀ s ∈ Ioo (-((3 * d / 4) / 2)) 0, ∀ z ∈ Metric.closedBall 0 ρ,
                  ‖iteratedFDeriv ℝ m (fun p : ℝ × E =>
                    (A.metric (p.1 + (-H.toReal + d / 4))).pullbackCoefficients
                      Φ p.2) (s, z)‖ ≤ B := by
  classical
  let U : TopologicalSpace.Opens G.limit.sliceCarrier.carrier :=
    ⟨G.exhaustion.space j, G.exhaustion.space_open j⟩
  let c := -H.toReal + d / 4
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : SecondCountableTopology G.limit.carrier.carrier :=
    G.limit.carrier.secondCountable
  obtain ⟨R, ρ, hρ, hρR, Φ, hsource, hzero, hmap, a0, b0, ha0, hb0, hanchor⟩ :=
    limitFinite_exists_original_anchor_bounds G P c hc j q hq
  let Candidates := {a : ℕ × RicciFlow 3 U (Icc (-(H.toReal + d / 2)) 0) //
    (∀ s ∈ Icc (-(H.toReal + d / 2)) 0, ∀ x : U,
      |(a.2.connection s).curvatureTensorNorm x| ≤ K) ∧
    ∃ ht : c ∈ Icc (-G.exhaustion.time a.1) 0,
      ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
        (a.2.metric c).inner x v w = (G.embedding a.1).pullbackInner c ht x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x w)}
  let l : Filter Candidates := Filter.comap (fun a : Candidates => a.val.1) atTop
  have hflows : ∀ a : Candidates, ∃ A : RicciFlow 3 U (Icc (-(3 * d / 4)) 0),
      (∀ s, A.metric s = a.val.2.metric (s + c)) ∧
      (∀ s ∈ Icc (-(3 * d / 4)) 0, ∀ x : U,
        |(A.connection s).curvatureTensorNorm x| ≤ K) ∧
      A.metric 0 = a.val.2.metric c := by
    intro a
    obtain ⟨A, hmetric, _hnorm, hcurv, hterminal, _hmem, _hclock⟩ :=
      limitFinite_endpoint_buffer_flow hd hc.1 a.val.2 a.property.1
    exact ⟨A, hmetric, hcurv, hterminal⟩
  choose A hmetric hcurv hterminalMetric using hflows
  have hraw : ∀ᶠ a in l, ∀ s ∈ Icc (-(3 * d / 4)) 0,
      ∀ x ∈ Φ '' Metric.ball 0 R, ((A a).connection s).curvatureTensorNorm x ≤ K :=
    Filter.Eventually.of_forall fun a s hs x _ =>
      (le_abs_self _).trans (hcurv a s hs x)
  obtain ⟨_Z0, _hZ0, hquadTail⟩ := hanchor 0
  have hquad : ∀ᶠ a in l, ∀ z ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
      a0 * ‖v‖ ^ 2 ≤ ((A a).metric 0).pullbackCoefficients Φ z v v ∧
        ((A a).metric 0).pullbackCoefficients Φ z v v ≤ b0 * ‖v‖ ^ 2 := by
    apply Filter.eventually_comap.mpr
    filter_upwards [hquadTail] with k hk a hak
    subst k
    obtain ⟨_ht, _hspace, hb⟩ := hk
    obtain ⟨ht, hread⟩ := a.property.2
    rw [hterminalMetric a]
    exact (hb _ hread).1
  have hterminal : ∀ m : ℕ, ∃ Z : ℝ, 1 ≤ Z ∧ ∀ᶠ a in l,
      ∀ z ∈ Metric.closedBall 0 ρ, ∀ n ≤ m,
        ‖iteratedFDeriv ℝ n (((A a).metric 0).pullbackCoefficients Φ) z‖ ≤ Z := by
    intro m
    obtain ⟨Z, hZ, htail⟩ := hanchor m
    refine ⟨Z, hZ, Filter.eventually_comap.mpr ?_⟩
    filter_upwards [htail] with k hk a hak
    subst k
    obtain ⟨_ht, _hspace, hb⟩ := hk
    obtain ⟨ht, hread⟩ := a.property.2
    rw [hterminalMetric a]
    exact (hb _ hread).2
  let f := fun a : Candidates => fun p : ℝ × E =>
    (a.val.2.metric (p.1 + c)).pullbackCoefficients Φ p.2
  have hactual : ∀ᶠ a in l, EqOn (f a)
      (fun p : ℝ × E => ((A a).metric p.1).pullbackCoefficients Φ p.2)
      (Ioo (-(3 * d / 4)) 0 ×ˢ Metric.ball 0 R) := by
    apply Filter.Eventually.of_forall
    intro a p _hp
    dsimp only [f]
    rw [hmetric a p.1]
  refine ⟨⟨by linarith, by linarith⟩, by ring, R, ρ, hρ, hρR, Φ,
    hsource, hzero, hmap, ?_⟩
  intro m
  obtain ⟨B, hB, hbound⟩ := limitFinite_chart_mixed_readout l (fun _ => U) P.m04
    (by linarith : 0 < 3 * d / 4) hK hρ hρR ha0 hb0 A (fun _ => Φ)
    (fun _ => hsource) hraw hquad hterminal f hactual m
  refine ⟨B, hB, ?_⟩
  filter_upwards [Filter.eventually_comap.mp hbound] with k hk ht F hF hread
  let a : Candidates := ⟨(k, F), hF, ht, hread⟩
  exact hk a rfl

end PoincareConjecture.M47
