import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Selected
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Cover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Diameter








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance projectiveAlternativeCarrierConnected {n : ℕ} (C : FlowCarrier n) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {M : Type} [TopologicalSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

namespace SelectedAncientRescalings

variable {b κ : ℝ} {F : RicciFlow 3 M (Iic b)} {p : M}
  (S : SelectedAncientRescalings F κ p)




theorem exists_terminal_round_or_projective_necks
    (P : M23NormalizedKappaCompactnessPredecessors) (hκ : 0 < κ)
    (hc : MetricComplete (F.metric b))
    (hop : ∀ x, (F.connection b).NonnegativeCurvatureOperator x)
    (hmono : ∀ s t, s ≤ t → t ≤ b → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ δ, 0 < δ ∧ δ < 1 ∧ ∃ B : RoundProductBlowup S δ,
      ((∃ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
          B.convergence.limitCarrier.carrier) (x : UnitTwoSphere),
        Φ (x, 0) = B.convergence.base ∧
        ∀ᶠ i in atTop, ∃ N : EpsilonNeck (F.metric b),
          N.epsilon = ε ∧
          N.scale = 1 / Real.sqrt ((F.connection b).scalarCurvature
            (S.center (B.convergence.subsequence i))) ∧
          N.center = S.center (B.convergence.subsequence i) ∧
          N.coordinate_map = (fun z => B.convergence.embedding i (Φ z))) ∨
        ∃ (Φ : RoundCylinderSpace → B.convergence.limitCarrier.carrier)
          (x : UnitTwoSphere),
          IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ ∧
          Function.Surjective Φ ∧ Φ (x, 0) = B.convergence.base ∧
          (∀ z w, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) ∧
          ∀ᶠ i in atTop,
            IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
              (B.convergence.embedding i ∘ Φ) (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
            (∀ z ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹, ∀ w ∈ univ ×ˢ Icc (-ε⁻¹) ε⁻¹,
              B.convergence.embedding i (Φ z) = B.convergence.embedding i (Φ w) ↔
                w = z ∨ w = (-z.1, z.2)) ∧
            B.convergence.embedding i (Φ (x, 0)) = S.center (B.convergence.subsequence i) ∧
            RoundCylinderClose ε 0 (fun z v w =>
              (F.connection b).scalarCurvature (S.center (B.convergence.subsequence i)) *
                roundCylinderPullback (F.metric b) (B.convergence.embedding i ∘ Φ) z v w) ∧
            (∃ e : RealProjectiveTwo ≃ₜ Set.range (fun q : UnitTwoSphere =>
                B.convergence.embedding i (Φ (q, 0))),
              ∀ q : UnitTwoSphere, (e (Quotient.mk realProjectiveTwoSetoid q)).val =
                B.convergence.embedding i (Φ (q, 0))) ∧
            ∀ q r : UnitTwoSphere,
              (F.metric b).edist (B.convergence.embedding i (Φ (q, 0)))
                (B.convergence.embedding i (Φ (r, 0))) ≤
                ENNReal.ofReal (Real.sqrt ((1 + ε) * 2 /
                  (F.connection b).scalarCurvature (S.center (B.convergence.subsequence i))) *
                    Real.pi)) := by
  obtain ⟨ηs, hηs, hsphere⟩ := S.exists_terminal_epsilonNeck_threshold P hε hεhalf
  obtain ⟨ηp, hηp, hprojective⟩ := S.exists_terminal_projectiveNeck_threshold P hε
  obtain ⟨δ, hδ, hδone, hδη, ⟨B⟩⟩ :=
    S.exists_roundProductBlowup P hκ hc hop hmono (min ηs ηp) (lt_min hηs hηp)
  refine ⟨δ, hδ, hδone, B, ?_⟩
  obtain ⟨_, hmodel⟩ := B.round.roundCylinder_or_projective_cover
    (B.convergence.limitFlow.metric 0) (B.convergence.limitFlow.connection 0)
    B.product (B.product_metric 0 le_rfl) B.convergence.base
  rcases hmodel with ⟨Φ, x, hx, hround⟩ | ⟨Φ, x, hΦ, hsurj, hx, hfiber, hround⟩
  · left
    refine ⟨Φ, x, hx, ?_⟩
    filter_upwards [hsphere hδ hδone.le (hδη.trans (min_le_left _ _))
      B.convergence (B.complete 0 hδ) B.scalar_base_ge Φ x hx hround] with i hi
    obtain ⟨N, hNε, hNs, hNcenter, _, hNmap⟩ := hi
    obtain ⟨A, hAε, hAs, hAcenter, _, hAmap, _, _⟩ :=
      S.exists_originalSliceNeck (B.convergence.subsequence i) N hNs
    exact ⟨A, hAε.trans hNε, hAs, hAcenter.trans hNcenter, hAmap.trans hNmap⟩
  · right
    refine ⟨Φ, x, hΦ, hsurj, hx, hfiber, ?_⟩
    filter_upwards [hprojective hδ hδone.le (hδη.trans (min_le_right _ _))
      B Φ x hΦ hx hfiber hround] with i hi
    refine ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2, ?_⟩
    intro q r
    apply edist_cylinderCover_slice_le (F.metric b) (B.convergence.embedding i ∘ Φ)
      hε (S.scalar_pos _) hi.1.contMDiffOn hi.2.2.2.1 q r
    exact ⟨neg_neg_of_pos (inv_pos.mpr hε), inv_pos.mpr hε⟩

end SelectedAncientRescalings

end PoincareConjecture.RicciFlow
