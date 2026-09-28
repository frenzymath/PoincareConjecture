import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.TerminalJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Terminal

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
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)

theorem exists_terminal_cylinderCover_closeness_threshold
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (radius k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hbase : ∀ k t, t ≤ 0 → ((F k).connection t).scalarCurvature (p k) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ η →
      ∀ G : AncientPointedGeometricConvergence C (fun k t => (F k).metric (t - δ)) p δ,
        G.limitCarrier.metricComplete (G.limitFlow.metric 0) →
        (1 / 2 : ℝ) ≤ (G.limitFlow.connection 0).scalarCurvature G.base →
      ∀ Φ : RoundCylinderSpace → G.limitCarrier.carrier,
        IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ →
        (fun z v w => (G.limitFlow.connection 0).scalarCurvature G.base *
          roundCylinderPullback (G.limitFlow.metric 0) Φ z v w) = EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, RoundCylinderClose ε 0
          (roundCylinderPullback ((F (G.subsequence i)).metric 0)
            (fun z => G.embedding i (Φ z))) := by
  let J := Icc (-ε⁻¹) ε⁻¹
  let d : ℕ := ⌊ε⁻¹⌋₊
  have hJ : IsCompact J := isCompact_Icc
  obtain ⟨C₀, Z, hC₀, hZ, hcompare⟩ :=
    exists_roundCylinder_buffered_comparison_constants hJ d
  obtain ⟨B, hB, hterminal⟩ := exists_terminal_cylinderCover_jet_constant C F p P
    hc hop radius hradius hbound hJ d
  obtain ⟨D, hD, hscalar⟩ := exists_buffered_limit_scalar_error_constant C F p P
    hc hop radius hradius hbound hnormalized hbase
  obtain ⟨η, hη, htolerance⟩ := exists_roundCylinder_terminal_error_tolerance
    hε hC₀ (show 0 ≤ B + 2 * D * Z by positivity)
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδone hδη G hcomplete hs Φ hΦ hround
  let s := (G.limitFlow.connection 0).scalarCurvature G.base
  obtain ⟨hgap, hsone⟩ := hscalar hδ G
  have htime := hterminal hδ hδone hs hsone G hcomplete Φ hΦ hround
  let Fseq (k : ℕ) := (F k).bufferedExpandingFlow δ
  have hab : (-1 : ℝ) < δ / 2 := by linarith
  have hbδ : δ / 2 ≤ δ := by linarith
  have hsub : ∀ k : ℕ, Ioo (-1) (δ / 2) ⊆ (fun t : ℝ => t - δ) ⁻¹' Iic 0 := by
    intro k t ht
    change t - δ ≤ 0
    linarith [ht.2]
  let W := G.window Fseq hab hbδ 0 hsub
  have hzero : (-1 : ℝ) < 0 ∧ 0 < δ / 2 := ⟨by norm_num, by linarith⟩
  let K : Set RoundCylinderCoordinates := {0} ×ˢ J
  have hK : IsCompact K := isCompact_singleton.prod hJ
  have hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ := by
    rintro x ⟨hx, _⟩
    exact ⟨by simpa only [mem_singleton_iff.mp hx] using
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)), mem_univ _⟩
  have hinitial := W.eventually_cylinder_parametrized_model_error_jets
    hzero hΦ.contMDiff hzero (by linarith : 0 < s) hround hK hKU d hη
  filter_upwards [htime, hinitial,
    G.eventually_cylinderCover_slab_regular Φ hΦ (-ε⁻¹) ε⁻¹] with i ht hi he
  let f : RoundCylinderSpace → (C (G.subsequence i)).carrier :=
    fun z => G.embedding i (Φ z)
  let U : Set RoundCylinderSpace := univ ×ˢ Ioo (-ε⁻¹) ε⁻¹
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U := he.contMDiffOn
  have hsmooth : RoundCylinderTensorSmoothOn ε
      (roundCylinderPullback ((F (G.subsequence i)).metric 0) f) := by
    simpa only [one_mul] using roundCylinderTensorSmoothOn_smul_pullback
      ((F (G.subsequence i)).metric 0) hf 1
  refine ⟨hsmooth, ε ^ 2 / 4, by nlinarith [sq_pos_of_pos hε], ?_⟩
  intro z hz
  have hzU : z ∈ U := ⟨mem_univ _, hz⟩
  have hzJ : z.2 ∈ J := ⟨hz.1.le, hz.2.le⟩
  apply (hcompare ((F (G.subsequence i)).metric (-δ))
    ((F (G.subsequence i)).metric 0) hU hf z hzU hzJ hs hsone hD.le hδ.le hB hη.le
      hgap ?_ ?_).trans (htolerance hδ.le hδη)
  · intro j hj
    have h := hi j hj z.1 (0, z.2) ⟨rfl, hzJ⟩
    change ‖iteratedFDeriv ℝ j
      (((F (G.subsequence i)).metric (0 + -δ)).parametrizedCoefficients
        (fun y => G.embedding i (Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm y.1, y.2))))
        (0, z.2) - s⁻¹ • iteratedFDeriv ℝ j roundCylinderModelCoefficients (0, z.2)‖ ≤ η at h
    rwa [zero_add] at h
  · intro j hj
    exact ht z.1 z.2 hzJ j hj

theorem exists_terminal_projectiveNeck_threshold
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (radius k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (hnormalized : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hbase : ∀ k t, t ≤ 0 → ((F k).connection t).scalarCurvature (p k) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ η →
      ∀ G : AncientPointedGeometricConvergence C (fun k t => (F k).metric (t - δ)) p δ,
        G.limitCarrier.metricComplete (G.limitFlow.metric 0) →
        (1 / 2 : ℝ) ≤ (G.limitFlow.connection 0).scalarCurvature G.base →
      ∀ (Φ : RoundCylinderSpace → G.limitCarrier.carrier) (x : UnitTwoSphere),
        IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ →
        Φ (x, 0) = G.base →
        (∀ z w, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) →
        (fun z v w => (G.limitFlow.connection 0).scalarCurvature G.base *
          roundCylinderPullback (G.limitFlow.metric 0) Φ z v w) = EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop,
          IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
            (G.embedding i ∘ Φ) (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
          (∀ z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹, ∀ w ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹,
            G.embedding i (Φ z) = G.embedding i (Φ w) ↔ w = z ∨ w = (-z.1, z.2)) ∧
          G.embedding i (Φ (x, 0)) = p (G.subsequence i) ∧
          RoundCylinderClose ε 0 (roundCylinderPullback ((F (G.subsequence i)).metric 0)
            (G.embedding i ∘ Φ)) := by
  obtain ⟨η, hη, hclose⟩ := exists_terminal_cylinderCover_closeness_threshold C F p P
    hc hop radius hradius hbound hnormalized hbase hε
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδone hδη G hcomplete hs Φ x hΦ hx hfiber hround
  filter_upwards [hclose hδ hδone hδη G hcomplete hs Φ hΦ hround,
    G.eventually_cylinderCover_slab_regular Φ hΦ (-ε⁻¹) ε⁻¹,
    G.eventually_cylinderCover_antipodal_fibers Φ hΦ.contMDiff.continuous hfiber (-ε⁻¹) ε⁻¹]
    with i hclose hlocal hfibers
  exact ⟨hlocal, hfibers, by rw [hx, G.base_preserving], hclose⟩

end PoincareConjecture.RawAncientSequence
