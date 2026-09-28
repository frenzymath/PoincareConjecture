import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalizedMetricJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceOrdinaryPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

theorem capPersistence_eventually_ordinary_neck_error
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
      let h := M13.scaleSmoothMetric (F.metric (p (C.subsequence k)).1)
        ((G).scalar (p (C.subsequence k))) (hp (C.subsequence k))
      let B : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
        roundCylinderPullback h (capOrdinaryEmbedding R p hp hd C k ∘ N.coordinate_map) z v w
      RoundCylinderTensorSmoothOn N.epsilon B ∧
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y => roundCylinderTensorCoefficient B
          (chartAt E₂ q) y a b - roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ tau := by
  filter_upwards [ordinaryChapter11_eventually_normalized_neck_error
    R p hp hd C hJ N m hm hK hNK tau htau hold] with k hk
  let h : RiemannianMetric 3 M := M13.scaleSmoothMetric (F.metric (p (C.subsequence k)).1)
    ((G).scalar (p (C.subsequence k))) (hp (C.subsequence k))
  let A : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
    generalizedCylinderPullback (C.embedding k) N.coordinate_map 0 z v w
  let B : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
    roundCylinderPullback h (capOrdinaryEmbedding R p hp hd C k ∘ N.coordinate_map) z v w
  have heq : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ v w : RoundCylinderTangent z, A z v w = B z v w := by
    intro z hz v w
    have hcoord := (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt
        (by simp)
    exact congrArg (fun r : ℝ => N.scale⁻¹ ^ 2 * r)
      (capPersistence_ordinary_cylinder_pullback_eq R p hp hd C k hcoord
        (hk.1 (hNK (N.coordinate_map_mem_of_axial_mem hz))) v w).symm
  refine ⟨hk.1, hk.2.1.congr_cylinder heq, ?_⟩
  intro q s hs j hj a b
  have hcoeff : (fun y => roundCylinderTensorCoefficient A (chartAt E₂ q) y a b -
      roundCylinderGram 0 (chartAt E₂ q) y a b) =ᶠ[𝓝 (0, s)]
        (fun y => roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
          roundCylinderGram 0 (chartAt E₂ q) y a b) := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (0, s) ∈ (univ : Set E₂) ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hs⟩)] with y hy
    exact congrArg (fun r => r - roundCylinderGram 0 (chartAt E₂ q) y a b)
      (heq ((chartAt E₂ q).symm y.1, y.2) hy.2 _ _)
  rw [← (hcoeff.iteratedFDeriv ℝ j).self_of_nhds]
  exact hk.2.2 q s hs j hj a b

end PoincareConjecture.M34
