import PoincareConjecture.Proofs.M32.Claim11_35.Transfer.UniformJets
import PoincareConjecture.Proofs.M32.Claim11_35.Transfer.BackwardFiniteJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderRegularity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem blowup_eventually_roundCylinderFamilyClose
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (Phi : RoundCylinderSpace → G.limit.sliceCarrier.carrier)
    (hPhi : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Phi)
    {delta : ℝ} (hdelta : 0 < delta)
    (hmodel : ∀ s ∈ Icc (-1 : ℝ) 0,
      roundCylinderPullback (G.limit.flow.metric s) Phi = EvolvingRoundCylinderMetric s) :
    ∀ᶠ k : ℕ in atTop, RoundCylinderFamilyClose delta (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback (G.embedding k) Phi) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_backwardRoundCylinderJetErrorSquared_bound delta⁻¹ ⌊delta⁻¹⌋₊
  let eta := min (1 : ℝ) (delta ^ 2 / (2 * (C + 1)))
  have hCpos : 0 < C + 1 := by linarith
  have hdeltaSq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have heta : 0 < eta := lt_min zero_lt_one (div_pos hdeltaSq (by positivity))
  have hetaOne : eta ≤ 1 := min_le_left _ _
  have hetaSq : eta ^ 2 ≤ eta := by nlinarith
  have hetaBound : (C + 1) * eta ≤ delta ^ 2 / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp
      (min_le_right (1 : ℝ) (delta ^ 2 / (2 * (C + 1))))
    change eta * (2 * (C + 1)) ≤ delta ^ 2 at h
    nlinarith
  have hstrict : C * eta ^ 2 < delta ^ 2 := by
    calc
      C * eta ^ 2 ≤ C * eta := mul_le_mul_of_nonneg_left hetaSq hC
      _ ≤ (C + 1) * eta := mul_le_mul_of_nonneg_right (by linarith) heta.le
      _ ≤ delta ^ 2 / 2 := hetaBound
      _ < delta ^ 2 := by linarith
  filter_upwards [blowup_uniform_cylinder_coefficientJets
    G hJI Phi hPhi delta⁻¹ ⌊delta⁻¹⌋₊ eta heta] with k hk
  obtain ⟨_htime, _hspace, hsmooth, hjets⟩ := hk
  constructor
  · intro s hs q a b p hp
    exact (hsmooth s (Ioc_subset_Icc_self hs) q p
      (Ioo_subset_Icc_self hp.2) a b).contDiffWithinAt
  · refine ⟨C * eta ^ 2, hstrict, ?_⟩
    intro s hs z hz
    have hs' : s ∈ Icc (-1 : ℝ) 0 := Ioc_subset_Icc_self hs
    have hz' : z.2 ∈ Icc (-delta⁻¹) delta⁻¹ := Ioo_subset_Icc_self hz
    apply hbound s hs' (generalizedCylinderPullback (G.embedding k) Phi s) z hz' eta heta.le
    · intro a b
      exact (hsmooth s hs' z.1 (0, z.2) hz' a b).sub
        (contDiff_roundCylinderGram s z.1 a b).contDiffAt
    · intro r hr a b
      have h := hjets z hz' s hs' r hr a b
      rw [hmodel s hs'] at h
      exact h.le

end PoincareConjecture.M32
