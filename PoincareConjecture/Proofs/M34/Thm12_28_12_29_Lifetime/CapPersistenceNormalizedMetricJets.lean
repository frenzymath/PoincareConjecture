import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceUniformMetricJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistencePullbackSmooth
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceTensorError











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold




theorem ordinaryChapter11_eventually_normalized_neck_error
    (p : ℕ → (G).point) (hp : ∀ k, 0 < (G).scalar (p k))
    (hd : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence (fixedFlowBlowupSequence (G) p hp hd) J)
    (hJ : UniqueDiffOn ℝ J) (N : EpsilonNeck (C.limit.flow.metric 0))
    (m : ℕ) (hm : m + 1 ≤ Nat.floor N.epsilon⁻¹)
    {K : Set C.limit.sliceCarrier.carrier} (hK : IsCompact K) (hNK : N.carrier ⊆ K)
    (tau : ℝ) (htau : 0 < tau)
    (hold : ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
            roundCylinderPullback (C.limit.flow.metric 0) N.coordinate_map z v w)
              (chartAt E₂ q) y a b - roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤
                tau / 2) :
    ∀ᶠ k : ℕ in atTop, K ⊆ C.exhaustion.space k ∧
      let B : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
        generalizedCylinderPullback (C.embedding k) N.coordinate_map 0 z v w
      RoundCylinderTensorSmoothOn N.epsilon B ∧
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient B
          (chartAt E₂ q) y a b - roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ tau := by
  let lambda := N.scale⁻¹ ^ 2
  have hlambda : 0 ≤ lambda := sq_nonneg _
  let rho := tau / (2 * (lambda + 1))
  have hrho : 0 < rho := div_pos htau (by positivity)
  have hprod : lambda * rho + tau / 2 ≤ tau := by
    have he : 2 * (lambda + 1) * rho = tau := by dsimp [rho]; field_simp
    nlinarith
  filter_upwards [ordinaryChapter11_eventually_neck_metricJets
    R p hp hd C hJ N m hm hK hNK rho hrho] with k hk
  let B := generalizedCylinderPullback (C.embedding k) N.coordinate_map 0
  let D := roundCylinderPullback (C.limit.flow.metric 0) N.coordinate_map
  have h0 : (0 : ℝ) ∈ Icc (-C.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  have hB : RoundCylinderTensorSmoothOn N.epsilon B :=
    capPersistence_generalizedCylinderPullback_smooth (C.embedding k)
      (C.exhaustion.space_open k) N.coordinate_map_smooth
        (fun _ hz => hk.1 (hNK (N.coordinate_map_mem_of_axial_mem hz.2))) h0
  have hD : RoundCylinderTensorSmoothOn N.epsilon D :=
    capPersistence_roundCylinderTensorSmoothOn_pullback
      (C.limit.flow.metric 0) N.coordinate_map_smooth
  refine ⟨hk.1, hB.const_mul, ?_⟩
  intro q s hs j hj a b
  have hx : (0, s) ∈ (chartAt E₂ q).target ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨?_, hs⟩
    simpa only [sphere_chart_center_zero] using
      (chartAt E₂ q).map_source (mem_chart_source E₂ q)
  exact (capPersistence_normalized_tensor_error_jet_le B D q s lambda j a b
    ((hB q a b).contDiffAt (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hx))
    ((hD q a b).contDiffAt (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hx))
    (hk.2 q s hs j hj a b).le (hold q s hs j hj a b)).trans
      (by simpa only [abs_of_nonneg hlambda] using hprod)

end PoincareConjecture.M34
