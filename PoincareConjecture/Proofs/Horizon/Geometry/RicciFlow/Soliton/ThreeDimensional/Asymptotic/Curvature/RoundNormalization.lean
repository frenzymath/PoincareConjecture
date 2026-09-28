import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.RoundBlowup
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.LimitScalar

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  RicciFlow.smallCarrier RicciFlow.smallChartedSpace RicciFlow.smallIsManifold
  uliftSecondCountable uliftConnected

local instance roundNormalizationConnected {n : ℕ} (C : FlowCarrier n) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

set_option maxHeartbeats 800000 in

theorem exists_scalar_normalized_round_surface_blowup_limit_of_unbounded_scalarCurvature
    (P : ThreeDimensionalClassificationPredecessors.{u}) (L : AncientAsymptoticSolitonLimitData S)
    {t₀ : ℝ} (ht₀ : t₀ < 0) (p : L.convergence.limit.carrier.carrier)
    (hunbounded : ¬ BddAbove
      (range (L.convergence.limit.flow.connection t₀).scalarCurvature))
    {η : ℝ} (hη : 0 < η) :
    ∃ (q : ℕ → L.convergence.limit.carrier.carrier) (r : ℕ → ℝ)
      (hQ : ∀ i, 0 < (L.convergence.limit.flow.connection t₀).scalarCurvature (q i)),
      let F := L.convergence.limit.flow
      let Q := fun i => (F.connection t₀).scalarCurvature (q i)
      let R := fun i => r i * Real.sqrt (Q i)
      let H := fun i =>
        (F.ulift : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).openAncientRescaleAt
          (Q i) (hQ i) t₀
      (∀ i, 0 < r i ∧
        (∀ x ∈ (F.metric t₀).ball (q i) (r i), (F.connection t₀).scalarCurvature x ≤ 4 * Q i) ∧
        ∀ s ≤ t₀, ∀ x ∈ (F.metric t₀).ball (q i) (r i),
          (F.connection s).curvatureTensorNorm x ≤ 36 * Q i) ∧
      Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop ∧
      Tendsto Q atTop atTop ∧ Tendsto R atTop atTop ∧
      Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal * Real.sqrt (Q i)) atTop atTop ∧
      Tendsto (fun i => r i / ((F.metric t₀).edist p (q i)).toReal) atTop (𝓝 0) ∧
      (∀ i, ((H i).connection 0).scalarCurvature (ULift.up (q i)) = 1) ∧
      ∃ ν : ℝ, 0 < ν ∧
        (∀ᶠ i in atTop, ENNReal.ofReal ν ≤
          ((H i).metric 0).volumeMeasure (((H i).metric 0).ball (ULift.up (q i)) 1)) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < η ∧
          ∃ G : AncientPointedGeometricConvergence
            (fun _ => (FlowCarrier.ofConnectedManifold 3
              (ULift.{u} L.convergence.limit.carrier.carrier)).shrink)
            (fun i t => (H i).shrink.metric (t - δ))
            (fun i => equivShrink (ULift.{u} L.convergence.limit.carrier.carrier)
              (ULift.up (q i))) δ,
            (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
            (1 / 2 : ℝ) ≤ 9 * (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
            ((1 / 2 : ℝ) ≤ (G.limitFlow.connection 0).scalarCurvature G.base ∧
              (G.limitFlow.connection 0).scalarCurvature G.base ≤ 1) ∧
            (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
             (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
               (G.limitFlow.connection t).curvatureTensorNorm x ≤ 36) ∧
             (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
               (G.limitFlow.connection t).NonnegativeCurvatureOperator x) ∧
             (letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
              ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base)) ∧
            let V := (G.limitFlow.ulift :
              RicciFlow 3 (ULift.{u} G.limitCarrier.carrier) (Iio δ))
            ∃ C : FlowCarrier.{u} 2,
              letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
              ∃ A : AncientKappaSolution 2 C.carrier,
                A.kappa = K.kappa / 1458 ∧
                Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
                ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
                    ULift.{u} G.limitCarrier.carrier,
                  (∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
                    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
                    (V.metric t).inner (e z)
                      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
                      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                        (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
                  (∀ t ≤ 0, ∀ x,
                    (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
                      (V.connection t).curvatureTensorNorm x) := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  obtain ⟨D, hD, hnormalization⟩ :=
    RicciFlow.exists_buffered_limit_scalar_normalization_constant_universal
      P.curvature (by norm_num : 0 < 2)
  have hη' : 0 < min η (1 / (2 * D)) := lt_min hη (by positivity)
  obtain ⟨q, r, hQ, hcontrol, hd, hQt, hRt, hdQ, hratio, hnormalize,
    ν, hν, hvolume, δ, hδ, hδone, hδη', G, hcomplete, hquant, hgeometry,
    hmodel⟩ :=
      L.exists_round_surface_blowup_limit_of_unbounded_scalarCurvature
        P ht₀ p hunbounded hη'
  let F := L.convergence.limit.flow
  let V : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  let Q := fun i => (F.connection t₀).scalarCurvature (q i)
  let R := fun i => r i * Real.sqrt (Q i)
  let H := fun i => V.openAncientRescaleAt (Q i) (hQ i) t₀
  have htime (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) : t₀ + s / Q i < 0 := by
    have h := (div_lt_iff₀ (hQ i)).mpr hs
    linarith
  have hwindow (i : ℕ) (a : ℝ) : Icc a 0 ⊆ interior (Iio (-t₀ * Q i)) := by
    rw [isOpen_Iio.interior_eq]
    intro s hs
    exact hs.2.trans_lt (mul_pos (neg_pos.mpr ht₀) (hQ i))
  have hcompleteH (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i)) :
      MetricComplete ((H i).metric s) := by
    apply V.parabolicRescale_metricComplete
    exact (F.ulift_metricComplete_iff _).mpr (L.convergence.limit.complete _ (htime i s hs))
  have hoperatorH (i : ℕ) (s : ℝ) (hs : s ∈ Iio (-t₀ * Q i))
      (x : ULift.{u} L.convergence.limit.carrier.carrier) :
      ((H i).connection s).NonnegativeCurvatureOperator x := by
    apply V.parabolicRescale_nonnegativeCurvatureOperator
    exact (F.ulift_nonnegativeCurvatureOperator_iff _ x).mpr
      (L.convergence.limit.nonnegative_curvature_operator _ (htime i s hs) x.down)
  have hball (i : ℕ) : ((H i).metric 0).ball (ULift.up (q i)) (R i) =
      (V.metric t₀).ball (ULift.up (q i)) (r i) := by
    change (rescaledMetric (V.metric (t₀ + 0 / Q i)) (Q i) (hQ i)).ball _ _ = _
    rw [rescaledMetric_ball_allDimensions, zero_div, add_zero]
    dsimp only [R]
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (hQ i)).ne']
  have hscalarH (i : ℕ) (s : ℝ) (hs : s ≤ 0)
      (x : ULift.{u} L.convergence.limit.carrier.carrier)
      (hx : x ∈ ((H i).metric 0).ball (ULift.up (q i)) (R i)) :
      ((H i).connection s).scalarCurvature x ≤ 4 := by
    have hst : t₀ + s / Q i ≤ t₀ :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)
    have hx' : x.down ∈ (F.metric t₀).ball (q i) (r i) := by
      have := (hball i) ▸ hx
      simpa only [RiemannianMetric.ball, Set.mem_ofPred_eq, V, F.ulift_edist] using this
    have hscalar := (L.convergence.limit.scalarCurvature_monotoneOn_of_derivative_nonnegative
      L.scalar_curvature_nonnegative_time_derivative x.down (hst.trans_lt ht₀) ht₀ hst).trans
        ((hcontrol i).2.1 x.down hx')
    dsimp only [H, RicciFlow.openAncientRescaleAt]
    rw [RicciFlow.parabolicRescale_scalarCurvature, F.ulift_scalarCurvature]
    have h := mul_le_mul_of_nonneg_left hscalar (inv_nonneg.mpr (hQ i).le)
    calc
      _ ≤ (Q i)⁻¹ * (4 * Q i) := h
      _ = 4 := by
        rw [← mul_assoc, mul_comm _ 4, mul_assoc, inv_mul_cancel₀ (hQ i).ne', mul_one]
  have hbaseH (i : ℕ) (s : ℝ) (hs : s ≤ 0) :
      ((H i).connection s).scalarCurvature (ULift.up (q i)) ≤ 1 := by
    have hst : t₀ + s / Q i ≤ t₀ :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)
    have hscalar := L.convergence.limit.scalarCurvature_monotoneOn_of_derivative_nonnegative
      L.scalar_curvature_nonnegative_time_derivative (q i) (hst.trans_lt ht₀) ht₀ hst
    dsimp only [H, RicciFlow.openAncientRescaleAt]
    rw [RicciFlow.parabolicRescale_scalarCurvature, F.ulift_scalarCurvature]
    exact (mul_le_mul_of_nonneg_left hscalar (inv_nonneg.mpr (hQ i).le)).trans_eq
      (inv_mul_cancel₀ (hQ i).ne')
  let A : ℕ → ℝ := fun i => (i : ℝ) + 1
  have hA : Tendsto A atTop atTop := tendsto_atTop_mono
    (fun i => show (i : ℝ) ≤ A i by dsimp [A]; linarith) tendsto_natCast_atTop_atTop
  have hscalarG := hnormalization
    (fun _ => FlowCarrier.ofConnectedManifold 3 (ULift.{u} L.convergence.limit.carrier.carrier))
    (fun i => Iio (-t₀ * Q i)) H (fun i => ULift.up (q i)) A R hA hRt
    (fun i => hwindow i (-A i))
    (fun i s hs => hcompleteH i s (interior_subset (hwindow i (-A i) hs)))
    (fun i s hs => hoperatorH i s (interior_subset (hwindow i (-A i) hs)))
    (fun i s hs => hscalarH i s hs.2) hnormalize
    (fun i s hs => hbaseH i s hs.2) hδ hδone.le G
  have hδD : δ * (2 * D) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 2 * D)).mp
      (hδη'.trans_le (min_le_right _ _))
  refine ⟨q, r, hQ, hcontrol, hd, hQt, hRt, hdQ, hratio, hnormalize,
    ν, hν, hvolume, δ, hδ, hδone, hδη'.trans_le (min_le_left _ _), G,
    hcomplete, hquant, ⟨?_, hscalarG.2⟩, hgeometry, hmodel⟩
  linarith [hscalarG.1]

end AncientAsymptoticSolitonLimitData

end PoincareConjecture
