import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckLocalMetricJets

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

private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

theorem ordinaryChapter11_uniform_neck_coefficientJets
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (N : EpsilonNeck (C.limit.flow.metric 0))
    {radius : ℝ} (hradius : radius < N.epsilon⁻¹)
    (m : ℕ) (rho : ℝ) (hrho : 0 < rho) :
    ∀ᶠ k : ℕ in atTop, ∀ z : RoundCylinderSpace, z.2 ∈ Icc (-radius) radius →
      ∀ s ∈ Icc (-1 : ℝ) 0, ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient
            (generalizedCylinderPullback (C.embedding k) N.coordinate_map s)
            (chartAt E₂ z.1) y a b -
          roundCylinderTensorCoefficient
            (roundCylinderPullback (C.limit.flow.metric s) N.coordinate_map)
            (chartAt E₂ z.1) y a b) (0, z.2)‖ < rho := by
  classical
  let K : Set RoundCylinderSpace := univ ×ˢ Icc (-radius) radius
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  let P := fun (k : ℕ) (z : RoundCylinderSpace) (s : ℝ) (j : ℕ) (a b : Fin 3) =>
    ‖iteratedFDeriv ℝ j (fun y =>
    roundCylinderTensorCoefficient
      (generalizedCylinderPullback (C.embedding k) N.coordinate_map s)
      (chartAt E₂ z.1) y a b -
    roundCylinderTensorCoefficient (roundCylinderPullback (C.limit.flow.metric s) N.coordinate_map)
      (chartAt E₂ z.1) y a b) (0, z.2)‖ < rho
  have hlocal (q : RoundCylinderSpace) : ∃ V : Set RoundCylinderSpace,
      V ∈ 𝓝 q ∧ ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, z ∈ V →
        ∀ s ∈ Icc (-1 : ℝ) 0, ∀ j ≤ m, ∀ a b : Fin 3, P k z s j a b := by
    by_cases hq : q ∈ K
    · have hqaxis : q.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
        ⟨(neg_lt_neg hradius).trans_le hq.2.1, hq.2.2.trans_lt hradius⟩
      obtain ⟨V, hV, hbound⟩ := ordinaryChapter11_locally_uniform_neck_coefficientJets
        R p hpositive hdiverges C hJ hJI N q hqaxis radius m rho hrho
      refine ⟨V, hV, ?_⟩
      filter_upwards [hbound] with k hk z hz hzV
      exact hk z hzV hz.2
    · refine ⟨Kᶜ, hK.isClosed.isOpen_compl.mem_nhds hq, ?_⟩
      filter_upwards [] with k z hz hzV
      exact False.elim (hzV hz)
  choose V hV hbound using hlocal
  obtain ⟨cover, _, hcover⟩ := hK.elim_nhds_subcover V (fun q _ => hV q)
  filter_upwards [cover.eventually_all.mpr (fun q _ => hbound q)] with k hk z hz
  have hzK : z ∈ K := ⟨mem_univ _, hz⟩
  obtain ⟨q, hq, hzq⟩ : ∃ q ∈ cover, z ∈ V q := by
    simpa only [mem_iUnion, exists_prop] using hcover hzK
  exact hk q hq z hzK hzq

end PoincareConjecture.M34
