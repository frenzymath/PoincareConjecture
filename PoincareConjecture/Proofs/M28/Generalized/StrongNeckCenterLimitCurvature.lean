import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.FixedCoordinateFlowCurvature
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckEighthPinching
import PoincareConjecture.Proofs.M28.Sec10_1_Pinching.OperatorPositivity
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Curvature.Calculus












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter PoincareConjecture.ChartDistance PoincareConjecture.SpacetimeBounds
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {epsilon : ℝ}
  (F : ℕ → GeneralizedRicciFlowData.{u}) (t : ℕ → ℝ)
  (S : ∀ i, GeneralizedStrongNeck (F i) (t i) epsilon)
  (H : ∀ i, RescaledRawCylinderData (C := (F i).slice (t i))
    (U := strongNeckOpen (S i)) (J := strongNeckBackwardInterval)
    (strongNeckCylinder (S i)) (GeneralizedStrongNeck.physical_interval_subset (S i)))

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in




theorem strongNeck_fixedCoordinate_limit_nonnegativeCurvatureOperator
    (P : RicciFlowCurvatureTheory.{u}) (V : Set E) (hV : IsOpen V) [Nonempty V]
    (e : ∀ i, V → strongNeckOpen (S i))
    (L : FixedCoordinateFlowLimit
      (fun i => GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i)) V hV e)
    (he : letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e i))
    (hpinch : ∀ i, generalizedWeakHamiltonIveyPinched (F i))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ i s, s ∈ Icc (-(1 / 8 : ℝ)) 0 → ∀ x : strongNeckOpen (S i),
      ((GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i)).connection s).curvatureTensorNorm
        x ≤ K)
    (hQ : Tendsto (fun i => (S i).scale⁻¹ ^ 2) atTop atTop) :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ s ∈ Icc (-(1 / 8 : ℝ)) 0, ∀ x : V,
      (L.flow.connection s).NonnegativeCurvatureOperator x := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro s hs x
  apply (L.flow.connection s).nonnegativeCurvatureOperator_of_plane_nonneg
    (L.flow.connection s).normalization_curvatureTensorCalculus x
  intro v w
  let f (k : ℕ) := chartParametrization (fun _ : Unit => V) (fun _ => hV)
    (i := ()) (e (L.subsequence k))
  let g (k : ℕ) :=
    (GeneralizedStrongNeck.rescaled_eighth_flow
      (S (L.subsequence k)) (H (L.subsequence k))).metric s
  let vsource (k : ℕ) := mfderiv (𝓡 3) (𝓡 3) (f k) x v
  let wsource (k : ℕ) := mfderiv (𝓡 3) (𝓡 3) (f k) x w
  have hQsub : Tendsto (fun k => (S (L.subsequence k)).scale⁻¹ ^ 2) atTop atTop :=
    hQ.comp L.subsequence_strictMono.tendsto_atTop
  have herr : Tendsto (fun k => GeneralizedStrongNeck.rescaled_eighth_pinching_error
      (S (L.subsequence k)) s hs (f k x)) atTop (𝓝 0) :=
    strongNeck_eighth_pinching_error_tendsto_zero P
      (fun k => F (L.subsequence k)) (fun k => t (L.subsequence k))
      (fun k => S (L.subsequence k)) (fun k => H (L.subsequence k))
      (fun k => hpinch (L.subsequence k)) hK
      (fun k a ha y => hcurv (L.subsequence k) a ha y) hQsub
      (fun _ => s) (fun _ => hs) (fun k => f k x)
  have hcoeff : Tendsto (fun k => (g k).pullbackCoefficients (f k) x) atTop
      (𝓝 (L.coefficients (s, x))) := by
    simpa only [metricTwoJet] using
      (L.spatial_twoJets (by norm_num) he s hs x.property).fst_nhds
  have heval (a b : E) : Tendsto (fun k => (g k).pullbackCoefficients (f k) x a b)
      atTop (𝓝 (L.coefficients (s, x) a b)) :=
    ((ContinuousLinearMap.apply ℝ ℝ b).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (_ →L[ℝ] ℝ) a).continuous.tendsto _).comp hcoeff)
  have hgram : Tendsto (fun k => M04.metricGram (g k) (f k x) (vsource k) (wsource k))
      atTop (𝓝 (L.coefficients (s, x) v v * L.coefficients (s, x) w w -
        L.coefficients (s, x) v w ^ 2)) :=
    ((heval v v).mul (heval w w)).sub ((heval v w).pow 2)
  have hlower : Tendsto
      (fun k => -GeneralizedStrongNeck.rescaled_eighth_pinching_error
        (S (L.subsequence k)) s hs (f k x) *
          M04.metricGram (g k) (f k x) (vsource k) (wsource k)) atTop (𝓝 0) := by
    simpa only [neg_zero, zero_mul] using herr.neg.mul hgram
  exact le_of_tendsto_of_tendsto hlower
    (L.curvatureTensor_tendsto (by norm_num) he s hs x v w v w)
    (Eventually.of_forall fun k => GeneralizedStrongNeck.rescaled_eighth_flow_plane_lower
      (S (L.subsequence k)) (H (L.subsequence k)) P s hs (f k x) (vsource k) (wsource k))

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in





theorem strongNeck_center_limit_readouts
    (P : RicciFlowCurvatureTheory.{u}) {R rho : ℝ} (hrho : 0 < rho) (hrhoR : 2 * rho < R)
    (Phi : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) E (strongNeckOpen (S i)) ∞)
    (hsource : ∀ i, (Phi i).source = Metric.ball 0 R)
    (hzero : ∀ i, Phi i 0 = strongNeckSourceCenter (S i))
    (horth : ∀ i v w, ((GeneralizedStrongNeck.rescaled_half_flow
      (S i) (H i)).metric 0).pullbackCoefficients
      (Phi i) 0 v w = inner ℝ v w)
    (hpinch : ∀ i, generalizedWeakHamiltonIveyPinched (F i))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ i s, s ∈ Icc (-(1 / 8 : ℝ)) 0 → ∀ x : strongNeckOpen (S i),
      ((GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i)).connection s).curvatureTensorNorm
        x ≤ K)
    (hQ : Tendsto (fun i => (S i).scale⁻¹ ^ 2) atTop atTop)
    (L : letI : Nonempty (Metric.ball (0 : E) rho) := ⟨⟨0, Metric.mem_ball_self hrho⟩⟩
      FixedCoordinateFlowLimit
        (fun i => GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i))
        (Metric.ball 0 rho) Metric.isOpen_ball (fun i x => Phi i x)) :
    letI : Nonempty (Metric.ball (0 : E) rho) := ⟨⟨0, Metric.mem_ball_self hrho⟩⟩
    letI := (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) rho)).isOpenEmbedding_subtypeVal
      |>.singletonChartedSpace
    letI := (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) rho)).isOpenEmbedding_subtypeVal
      |>.isManifold_singleton (I := 𝓡 3) (n := ∞)
    (∀ s ∈ Icc (-(1 / 8 : ℝ)) 0, ∀ x : Metric.ball (0 : E) rho,
      (L.flow.connection s).NonnegativeCurvatureOperator x) ∧
    (L.flow.connection 0).scalarCurvature ⟨0, Metric.mem_ball_self hrho⟩ = 1 ∧
    ∀ v w : E, (L.flow.metric 0).inner ⟨0, Metric.mem_ball_self hrho⟩ v w = inner ℝ v w := by
  classical
  let V : Set E := Metric.ball 0 rho
  let hV : IsOpen V := Metric.isOpen_ball
  let : Nonempty V := ⟨⟨0, Metric.mem_ball_self hrho⟩⟩
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  let e : ∀ i, V → strongNeckOpen (S i) := fun i x => Phi i x
  let x0 : V := ⟨0, Metric.mem_ball_self hrho⟩
  have hVU : V ⊆ Metric.ball 0 R := Metric.ball_subset_ball (by linarith)
  have he : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e i) := by
    intro i x
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) V hV ∞ x).comp
      (𝓡 3) (strongNeckOpen (S i))
      ((Phi i).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ ((hsource i).symm ▸ hVU x.property))
  have htime : (0 : ℝ) ∈ Icc (-(1 / 8 : ℝ)) 0 := by norm_num
  refine ⟨strongNeck_fixedCoordinate_limit_nonnegativeCurvatureOperator
    F t S H P V hV e L he hpinch hK hcurv hQ, ?_, ?_⟩
  · have hsourceScalar (i : ℕ) :
        ((GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i)).connection 0).scalarCurvature
          (Phi i 0) = 1 := by
      change ((GeneralizedStrongNeck.rescaled_half_flow (S i) (H i)).connection 0).scalarCurvature
        (Phi i 0) = 1
      rw [hzero i]
      exact GeneralizedStrongNeck.rescaled_half_scalar_at_center (S i) (H i)
    have hconv := L.scalarCurvature_tendsto (by norm_num) he 0 htime x0
    have hconst : Tendsto
        (fun k => ((GeneralizedStrongNeck.rescaled_eighth_flow
          (S (L.subsequence k)) (H (L.subsequence k))).connection 0).scalarCurvature
            (Phi (L.subsequence k) 0)) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun k => (hsourceScalar (L.subsequence k)).symm
    exact tendsto_nhds_unique hconv hconst
  · intro v w
    have hparam (i : ℕ) :
        chartParametrization (fun _ : Unit => V) (fun _ => hV) (i := ()) (e i) =ᶠ[𝓝 (0 : E)]
          (Phi i) :=
      Filter.mem_of_superset (hV.mem_nhds (Metric.mem_ball_self hrho))
        (fun y hy => chartParametrization_apply (fun _ : Unit => V) (fun _ => hV)
          (e i) ⟨y, hy⟩)
    have hsourceInner (i : ℕ) :
        ((GeneralizedStrongNeck.rescaled_eighth_flow (S i) (H i)).metric 0).pullbackCoefficients
            (chartParametrization (fun _ : Unit => V) (fun _ => hV) (i := ()) (e i))
            0 v w = inner ℝ v w := by
      change ((GeneralizedStrongNeck.rescaled_half_flow (S i) (H i)).metric 0).pullbackCoefficients
        _ 0 v w = _
      rw [((GeneralizedStrongNeck.rescaled_half_flow
        (S i) (H i)).metric 0).pullbackCoefficients_eq_of_eventuallyEq
        (hparam i)]
      exact horth i v w
    have hconv := L.metric_inner_tendsto (by norm_num) he 0 htime x0 v w
    have hconst : Tendsto
        (fun k => ((GeneralizedStrongNeck.rescaled_eighth_flow
          (S (L.subsequence k)) (H (L.subsequence k))).metric 0).pullbackCoefficients
            (chartParametrization (fun _ : Unit => V) (fun _ => hV)
              (i := ()) (e (L.subsequence k))) 0 v w) atTop (𝓝 (inner ℝ v w)) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun k => (hsourceInner (L.subsequence k)).symm
    exact tendsto_nhds_unique hconv hconst

end PoincareConjecture.M28
