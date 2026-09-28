import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.TerminalCloseness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)

theorem exists_terminal_epsilonNeck_threshold
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (radius k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hbase : ∀ k t, t ≤ 0 → ((F k).connection t).scalarCurvature (p k) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ η →
      ∀ G : AncientPointedGeometricConvergence C (fun k t => (F k).metric (t - δ)) p δ,
        G.limitCarrier.metricComplete (G.limitFlow.metric 0) →
        (1 / 2 : ℝ) ≤ (G.limitFlow.connection 0).scalarCurvature G.base →
      ∀ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
        (q : UnitTwoSphere), Φ (q, 0) = G.base →
        (fun z v w => (G.limitFlow.connection 0).scalarCurvature G.base *
          roundCylinderPullback (G.limitFlow.metric 0) Φ z v w) = EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, ∃ N : EpsilonNeck ((F (G.subsequence i)).metric 0),
          N.epsilon = ε ∧ N.scale = 1 ∧ N.center = p (G.subsequence i) ∧
          N.connection = (F (G.subsequence i)).connection 0 ∧
          N.coordinate_map = (fun z => G.embedding i (Φ z)) := by
  obtain ⟨η, hη, hclose⟩ := exists_terminal_cylinder_closeness_threshold C F p P
    hc hop radius hradius hbound hnormalized hbase hε
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδone hδη G hcomplete hs Φ q hq hround
  have hcl := hclose hδ hδone hδη G hcomplete hs Φ hround
  let Fseq (k : ℕ) := (F k).bufferedExpandingFlow δ
  have hab : (-1 : ℝ) < δ / 2 := by linarith
  have hbδ : δ / 2 ≤ δ := by linarith
  have hsub : ∀ k : ℕ, Ioo (-1) (δ / 2) ⊆ (fun t : ℝ => t - δ) ⁻¹' Iic 0 := by
    intro k t ht
    change t - δ ≤ 0
    linarith [ht.2]
  let W := G.window Fseq hab hbδ 0 hsub
  have hzero : (-1 : ℝ) < 0 ∧ 0 < δ / 2 := ⟨by norm_num, by linarith⟩
  filter_upwards [hcl, W.eventually_cylinderSlabEmbedding hzero Φ hε] with i hclose he
  let e := W.cylinderSlabEmbedding hzero Φ ε i
  have hemap : (e : RoundCylinderSpace → (C (G.subsequence i)).carrier) =
      (fun z => G.embedding i (Φ z)) := rfl
  obtain ⟨hsource, hsmooth, hinverse, _⟩ := he
  have hcentral : e '' (univ ×ˢ ({0} : Set ℝ)) ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    apply e.map_source
    rw [hsource]
    have hpos := inv_pos.mpr hε
    exact ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ from ⟨neg_neg_of_pos hpos, hpos⟩)⟩
  refine ⟨{
    epsilon := ε
    epsilon_pos := hε
    epsilon_lt_half := hεhalf
    scale := 1
    scale_pos := zero_lt_one
    center := p (G.subsequence i)
    connection := (F (G.subsequence i)).connection 0
    scalar_center_pos := by rw [hnormalized]; exact zero_lt_one
    scale_eq_scalar := by rw [hnormalized, Real.one_rpow]
    carrier := e.target
    carrier_open := e.open_target
    coordinate := neckDomainCoordinates e hsource
    coordinate_map := e
    coordinate_map_eq := fun z => rfl
    coordinate_map_smooth := hsmooth
    coordinate_inverse := e.symm
    coordinate_inverse_mem := fun x hx => neckDomainCoordinates_inverse_mem e hsource hx
    coordinate_inverse_left := neckDomainCoordinates_inverse_left e hsource
    coordinate_inverse_right := neckDomainCoordinates_inverse_right e hsource
    coordinate_inverse_smooth := hinverse
    central_sphere := e '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := ?_
    central_sphere_subset := hcentral
    metric_comparison := ⟨by
      simpa only [inv_one, one_pow, one_mul, hemap] using hclose⟩
  }, rfl, rfl, rfl, rfl, hemap⟩
  refine ⟨(q, 0), ⟨mem_univ _, mem_singleton _⟩, ?_⟩
  change G.embedding i (Φ (q, 0)) = p (G.subsequence i)
  rw [hq, G.base_preserving]

end PoincareConjecture.RawAncientSequence
