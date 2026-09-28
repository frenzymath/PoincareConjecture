import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Rescaling










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace BasedKappaSolution

variable {kappa : ℝ} (B : BasedKappaSolution kappa)

local instance sequenceTermTopologicalSpace : TopologicalSpace B.carrier.carrier := B.carrier.topologicalSpace
local instance sequenceTermMeasurableSpace : MeasurableSpace B.carrier.carrier := B.carrier.measurableSpace
local instance sequenceTermBorelSpace : BorelSpace B.carrier.carrier := B.carrier.borelSpace
local instance sequenceTermChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) B.carrier.carrier :=
  B.carrier.chartedSpace
local instance sequenceTermIsManifold : IsManifold (𝓡 3) ∞ B.carrier.carrier := B.carrier.isManifold
local instance sequenceTermT2Space : T2Space B.carrier.carrier := B.carrier.t2Space
local instance sequenceTermT3Space : T3Space B.carrier.carrier := B.carrier.t3Space
local instance sequenceTermSecondCountable : SecondCountableTopology B.carrier.carrier := B.carrier.secondCountable
local instance sequenceTermConnectedSpace : ConnectedSpace B.carrier.carrier := B.connectedSpace



theorem exists_whole_past_curvature_bound
    (P : M23NormalizedKappaCompactnessPredecessors) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≤ 0 → ∀ x : B.carrier.carrier,
      |(B.flow.flow.connection t).curvatureTensorNorm x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := B.flow.bounded_curvature 0 le_rfl
  refine ⟨3 * C, by positivity, ?_⟩
  intro t ht x
  rw [abs_of_nonneg (show 0 ≤ (B.flow.flow.connection t).curvatureTensorNorm x from
    Real.sqrt_nonneg _)]
  exact (P.past_norm_le_scalar B.carrier.carrier B.flow t 0 ht le_rfl x).trans
    (((B.flow.flow.connection 0).scalarCurvature_le_curvatureTensorNorm_sharp x).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbound x)) (by norm_num)))

end BasedKappaSolution

namespace NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance sequenceCarrierConnected (C : FlowCarrier 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)



theorem allTimeCurvatureControl_of_eventually
    (P : M23NormalizedKappaCompactnessPredecessors)
    (heventual : ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ t : ℝ, t ≤ 0 → ∀ x : (S.term k).carrier.carrier,
        x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base r →
          |((S.term k).flow.flow.connection t).curvatureTensorNorm x| ≤ C) :
    M23AllTimeCurvatureControl S := by
  classical
  choose B hB hbound using fun k ↦ (S.term k).exists_whole_past_curvature_bound P
  intro r hr
  obtain ⟨C, hC, heventual⟩ := heventual r hr
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventual
  refine ⟨C + ∑ j ∈ Finset.range N, B j, add_nonneg hC
    (Finset.sum_nonneg fun j _ ↦ hB j), ?_⟩
  intro k
  change ∀ t : ℝ, t ≤ 0 → ∀ x : (S.term k).carrier.carrier,
    x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base r →
      |((S.term k).flow.flow.connection t).curvatureTensorNorm x| ≤ _
  intro t ht x hx
  by_cases hk : N ≤ k
  · exact (hN k hk t ht x hx).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ hB j))
  · have hkN : k ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hk)
    exact (hbound k t ht x).trans
      ((Finset.single_le_sum (fun j _ ↦ hB j) hkN).trans (le_add_of_nonneg_left hC))



theorem allTimeCurvatureControl_of_expanding_balls
    (P : M23NormalizedKappaCompactnessPredecessors) (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, ∀ t : ℝ, t ≤ 0 → ∀ x : (S.term k).carrier.carrier,
      x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base (L k) →
        |((S.term k).flow.flow.connection t).curvatureTensorNorm x| ≤ C) :
    M23AllTimeCurvatureControl S := by
  apply S.allTimeCurvatureControl_of_eventually P
  intro r _
  refine ⟨C, hC, ?_⟩
  filter_upwards [hL.eventually_ge_atTop r] with k hk t ht x hx
  exact hbound k t ht x (lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hk))

end NormalizedKappaSolutionSequence

section VaryingCarriers

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance varyingSequenceCarrierConnected (C : FlowCarrier 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected





theorem m23_exists_controlled_sequence_of_unbounded_curvature_scale
    (P : M23NormalizedKappaCompactnessPredecessors)
    (C : ℕ → FlowCarrier 3) (K : ∀ k, AncientKappaSolution 3 (C k).carrier)
    {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 ≤ ν) (hkappa : ∀ k, (K k).kappa = κ)
    (p x : ∀ k, (C k).carrier) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hx : ∀ k, x k ∈ ((K k).flow.metric 0).ball (p k) (r k))
    (hvolume : ∀ k, ENNReal.ofReal (ν * r k ^ 3) ≤
      calibratedMetricVolume ((K k).flow.metric 0) (((K k).flow.metric 0).ball (p k) (r k)))
    (hscale : Tendsto (fun k ↦ r k ^ 2 * ((K k).flow.connection 0).scalarCurvature (x k))
      atTop atTop) :
    ∃ S : NormalizedKappaSolutionSequence κ,
      (∀ k, (S.term k).carrier = C k) ∧ M23AllTimeCurvatureControl S ∧
      (∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
        ∀ t : ℝ, t ≤ 0 → ∀ y ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base a,
          |((S.term k).flow.flow.connection t).curvatureTensorNorm y| ≤ 4) ∧
      ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
        ENNReal.ofReal ((ν / 27) * a ^ 3) ≤
          calibratedMetricVolume ((S.term k).flow.flow.metric 0)
            (((S.term k).flow.flow.metric 0).ball (S.term k).base a) := by
  classical
  choose G q L hGk hLpos hLeq hnorm hbound hvol using fun k ↦
    m23_exists_normalized_controlled_rescaling P (K k) (p k) (x k)
      (hr k) hν (hx k) (hvolume k)
  let S : NormalizedKappaSolutionSequence κ := {
    kappa_pos := hκ
    term := fun k ↦ {
      carrier := C k
      connectedSpace := connectedSpace_iff_univ.mpr (C k).connected
      flow := G k
      base := q k
      kappa_eq := (hGk k).trans (hkappa k)
      scalar_normalized := hnorm k
    }
  }
  have hL : Tendsto L atTop atTop := by
    have h := (Real.tendsto_sqrt_atTop.comp hscale).atTop_div_const (by norm_num : (0 : ℝ) < 2)
    convert h using 1
    ext k
    rw [hLeq k, Function.comp_apply, Real.sqrt_mul (sq_nonneg (r k)),
      Real.sqrt_sq (hr k).le]
  refine ⟨S, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · exact S.allTimeCurvatureControl_of_expanding_balls P L hL (by norm_num) hbound
  · intro a _
    filter_upwards [hL.eventually_ge_atTop a] with k hk t ht y hy
    exact hbound k t ht y (lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hk))
  · intro a ha
    filter_upwards [hL.eventually_ge_atTop a] with k hk
    exact hvol k a ha hk

end VaryingCarriers

end PoincareConjecture
