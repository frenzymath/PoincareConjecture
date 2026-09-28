import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.BufferedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SelectedRoundFactor










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

local instance roundBlowupConnected {n : ℕ} (C : FlowCarrier n) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}



theorem exists_round_surface_blowup_limit_of_unbounded_scalarCurvature
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
  obtain ⟨q, r, hQ, hcontrol, hd, hQt, hRt, hdQ, hratio, hnormalize,
    ν, hν, hvolume, δ, hδ, hδone, hδη, G, hcomplete, hquant, hnonflat, hbound,
    hop, hline⟩ :=
      L.exists_nonflat_ancient_blowup_limit_of_unbounded_scalarCurvature_lt
        P.curvature ht₀ p hunbounded hη
  refine ⟨q, r, hQ, hcontrol, hd, hQt, hRt, hdQ, hratio, hnormalize,
    ν, hν, hvolume, δ, hδ, hδone, hδη, G, hcomplete, hquant,
    ⟨hnonflat, hbound, hop, hline⟩, ?_⟩
  exact L.exists_compact_round_surface_product_of_selected_blowup_limit
    P ht₀ q (fun i => (L.convergence.limit.flow.connection t₀).scalarCurvature (q i))
    hQ hδ G hcomplete hnonflat hbound hop hline

end AncientAsymptoticSolitonLimitData

end PoincareConjecture
