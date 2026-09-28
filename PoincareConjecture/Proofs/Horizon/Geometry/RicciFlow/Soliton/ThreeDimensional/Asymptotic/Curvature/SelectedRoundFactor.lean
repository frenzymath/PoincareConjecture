import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.RoundFactor

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  RicciFlow.smallCarrier RicciFlow.smallChartedSpace RicciFlow.smallIsManifold
  uliftSecondCountable uliftConnected

local instance selectedRoundFactorConnected {n : ℕ} (C : FlowCarrier n) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem exists_compact_round_surface_product_of_selected_blowup_limit
    (P : ThreeDimensionalClassificationPredecessors.{u})
    (L : AncientAsymptoticSolitonLimitData S) {t₀ : ℝ} (ht₀ : t₀ < 0) :
    ∀ (q : ℕ → L.convergence.limit.carrier.carrier) (Q : ℕ → ℝ)
      (hQ : ∀ i, 0 < Q i) {δ : ℝ}, 0 < δ →
      let F := L.convergence.limit.flow
      let H := fun i =>
        (F.ulift : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).openAncientRescaleAt
          (Q i) (hQ i) t₀
      ∀ G : AncientPointedGeometricConvergence
        (fun _ => (FlowCarrier.ofConnectedManifold 3
          (ULift.{u} L.convergence.limit.carrier.carrier)).shrink)
        (fun i t => (H i).shrink.metric (t - δ))
        (fun i => equivShrink (ULift.{u} L.convergence.limit.carrier.carrier)
          (ULift.up (q i))) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) →
        0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base →
        (∀ t ∈ Iio δ, ∀ x, (G.limitFlow.connection t).curvatureTensorNorm x ≤ 36) →
        (∀ t ∈ Iio δ, ∀ x, (G.limitFlow.connection t).NonnegativeCurvatureOperator x) →
        (letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
          ∃ γ : ℝ → G.limitCarrier.carrier, Isometry γ ∧ γ 0 = G.base) →
        let V := (G.limitFlow.ulift : RicciFlow 3 (ULift.{u} G.limitCarrier.carrier) (Iio δ))
        ∃ C : FlowCarrier.{u} 2,
          letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
          ∃ A : AncientKappaSolution 2 C.carrier,
            A.kappa = K.kappa / 1458 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
            ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
                ULift.{u} G.limitCarrier.carrier,
              (∀ (t : ℝ), t ≤ 0 → ∀ (z : C.carrier × ℝ)
                (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
                (V.metric t).inner (e z)
                  (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
                  (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                    (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
              (∀ (t : ℝ), t ≤ 0 → ∀ x,
                (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
                  (V.connection t).curvatureTensorNorm x) := by
  intro q Q hQ δ hδ
  dsimp only
  intro G hc hn hb hop hline
  let V : RicciFlow 3 (ULift.{u} G.limitCarrier.carrier) (Iio δ) := G.limitFlow.ulift
  let W := Poincare.Geometry.RicciFlow.Harnack.restrictFlow V
    (show Iic (0 : ℝ) ⊆ Iio δ from fun _ ht => ht.trans_lt hδ)
    ordConnected_Iic (show (Iic (0 : ℝ)).Nontrivial from
      ⟨-1, by norm_num, 0, by simp, by norm_num⟩)
  have hcomplete : ∀ t ≤ 0, MetricComplete (W.metric t) := by
    intro t ht
    exact (G.limitFlow.ulift_metricComplete_iff t).mpr (hc t (ht.trans_lt hδ))
  have hoperator : ∀ t ≤ 0, ∀ x, (W.connection t).NonnegativeCurvatureOperator x := by
    intro t ht x
    exact (G.limitFlow.ulift_nonnegativeCurvatureOperator_iff t x).mpr
      (hop t (ht.trans_lt hδ) x.down)
  have hbound : ∀ t ≤ 0, ∀ x, (W.connection t).curvatureTensorNorm x ≤ 36 := by
    intro t ht x
    simpa only [W, V, Poincare.Geometry.RicciFlow.Harnack.restrictFlow,
      G.limitFlow.ulift_curvatureTensorNorm] using hb t (ht.trans_lt hδ) x.down
  have hstatic := L.metricKappaNoncollapsed_of_selected_blowup_limit
    P.curvature ht₀ q Q hQ hδ G hc
  have hstaticV : ∀ t ∈ Iio δ,
      MetricKappaNoncollapsed (V.metric t) (V.connection t) (K.kappa / 729) := by
    intro t ht
    exact G.limitFlow.metricKappaNoncollapsed_ulift t (hstatic t ht)
  have hnoncollapse : AncientKappaNoncollapsed W (K.kappa / 729) :=
    V.ancientKappaNoncollapsed_restrict_of_metricKappaNoncollapsed hδ hstaticV
  have hscalar : ∃ p, 0 < (W.connection 0).scalarCurvature p := by
    refine ⟨ULift.up G.base, ?_⟩
    have hpositive : 0 < (W.connection 0).curvatureTensorNorm (ULift.up G.base) := by
      simpa only [W, V, Poincare.Geometry.RicciFlow.Harnack.restrictFlow,
        G.limitFlow.ulift_curvatureTensorNorm] using hn
    have hcompare := (W.connection 0).curvatureTensorNorm_le_scalarCurvature
      (P.curvature.tensor_calculus 3 (ULift.{u} G.limitCarrier.carrier)
        (W.metric 0) (W.connection 0)) (ULift.up G.base) (hoperator 0 le_rfl _)
    norm_num at hcompare
    nlinarith
  let := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
  obtain ⟨γ, hγ, _⟩ := hline
  let γlift : ℝ → ULift.{u} G.limitCarrier.carrier := fun s => ULift.up (γ s)
  have hγlift : ∀ s t : ℝ, (W.metric 0).edist (γlift s) (γlift t) =
      ENNReal.ofReal |s - t| := by
    intro s t
    rw [show (W.metric 0).edist (γlift s) (γlift t) =
      (G.limitFlow.metric 0).edist (γ s) (γ t) from G.limitFlow.ulift_edist 0 _ _]
    change edist (γ s) (γ t) = ENNReal.ofReal |s - t|
    rw [hγ.edist_eq, edist_dist, Real.dist_eq]
  obtain ⟨C, A, hconstant, hround, e, hmetric, hnorm⟩ :=
    W.exists_compact_round_surface_product_of_minimizing_line P hcomplete hoperator
      (by norm_num : (0 : ℝ) ≤ 36) hbound (div_pos K.kappa_pos (by norm_num))
      hnoncollapse hscalar γlift hγlift
  refine ⟨C, A, ?_, hround, e, hmetric, hnorm⟩
  calc
    A.kappa = (K.kappa / 729) / 2 := hconstant
    _ = K.kappa / 1458 := by ring

end PoincareConjecture.AncientAsymptoticSolitonLimitData
