import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.NormalizedJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CenteredTensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Comparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_late_static_neck_terminal_comparison
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    {ε l u : ℝ} (hεpos : 0 < ε) (hε : ε ≤ 1 / 200) (hl : 0 < l) (hu : 0 < u) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ N : EpsilonNeck ((H.terminalFlow P04).metric t),
        N.epsilon = ε → N.carrier ⊆ A →
        l ≤ N.connection.scalarCurvature N.center →
        N.connection.scalarCurvature N.center ≤ u →
        0 < ((H.terminalFlow P04).connection T).scalarCurvature N.center ∧
        RoundCylinderClose (2 * ε) 0 (fun z v w =>
          ((H.terminalFlow P04).connection T).scalarCurvature N.center *
            roundCylinderPullback ((H.terminalFlow P04).metric T) N.coordinate_map z v w) := by
  have hweak : ε ≤ 2 * ε := by linarith
  let m := ⌊(2 * ε)⁻¹⌋₊
  have hm : m ≤ ⌊ε⁻¹⌋₊ := Nat.floor_mono
    ((inv_le_inv₀ (mul_pos (by norm_num) hεpos) hεpos).2 hweak)
  obtain ⟨η, hη, htolerance⟩ := TerminalNeck.exists_staticCylinder_comparison_tolerance hεpos
    (show ε < 2 * ε by linarith)
  obtain ⟨C, hC, hcoeff⟩ := exists_cylinder_coefficient_jet_constant m
  obtain ⟨s, hs, hsT, hsmall⟩ := H.exists_late_static_neck_normalized_jet_small
    P04 hA hε hl hu m hm (div_pos hη hC)
  refine ⟨s, hs, hsT, ?_⟩
  intro t ht N hNε hNA hql hqu
  obtain ⟨hQ, hjet⟩ := hsmall t ht N hNε hNA hql hqu
  let Q := ((H.terminalFlow P04).connection T).scalarCurvature N.center
  let q := N.connection.scalarCurvature N.center
  let B₁ : RoundCylinderTwoTensor := fun z v w => Q *
    roundCylinderPullback ((H.terminalFlow P04).metric T) N.coordinate_map z v w
  let B₀ : RoundCylinderTwoTensor := fun z v w => q *
    roundCylinderPullback ((H.terminalFlow P04).metric t) N.coordinate_map z v w
  have hpow : N.scale⁻¹ ^ 2 = q := by
    rw [N.scale_eq_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, inv_inv,
      ← Real.rpow_natCast, ← Real.rpow_mul N.scalar_center_pos.le]
    norm_num [q]
  have hclose : RoundCylinderClose ε 0 B₀ := by
    simpa only [B₀, q, hpow, hNε] using N.metric_comparison.close
  refine ⟨hQ, htolerance B₀ B₁ hclose ?_ ?_⟩
  · apply roundCylinderTensorSmoothOn_smul_pullback
    apply N.coordinate_map_smooth.mono
    rw [hNε]
    exact prod_mono subset_rfl (DeepHorn.neckInterval_subset hεpos hweak)
  · intro z hz j hj a b
    have hzold : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hNε]
      exact DeepHorn.neckInterval_subset hεpos hweak hz
    let f := centeredNeckLift N z.1 z.2
    let gT := ((H.terminalFlow P04).metric T).pullbackCoefficients f
    let gt := ((H.terminalFlow P04).metric t).pullbackCoefficients f
    have hf := centeredNeckLift_contMDiffAt N z.1 z.2 (zero_mem_centeredNeckDomain N hzold)
    have hgT := ((H.terminalFlow P04).metric T).contDiffAt_pullbackCoefficients hf
    have hgt := ((H.terminalFlow P04).metric t).contDiffAt_pullbackCoefficients hf
    have hlocal : (fun p : E => centeredCylinderMetric B₁ z.1 z.2 p -
        centeredCylinderMetric B₀ z.1 z.2 p) =ᶠ[𝓝 0] fun p => Q • gT p - q • gt p := by
      filter_upwards [(centeredNeckDomain_isOpen N z.2).mem_nhds
        (zero_mem_centeredNeckDomain N hzold)] with p hp
      rw [centeredCylinderMetric_smul, centeredCylinderMetric_smul,
        centeredCylinderMetric_pullback _ N.coordinate_map_smooth _ _ hp,
        centeredCylinderMetric_pullback _ N.coordinate_map_smooth _ _ hp]
      rfl
    have hsmooth : ContDiffAt ℝ ∞ (fun p : E => centeredCylinderMetric B₁ z.1 z.2 p -
        centeredCylinderMetric B₀ z.1 z.2 p) 0 :=
      ((hgT.const_smul Q).sub (hgt.const_smul q)).congr_of_eventuallyEq hlocal
    have hjs : ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun p : E =>
        centeredCylinderMetric B₁ z.1 z.2 p - centeredCylinderMetric B₀ z.1 z.2 p) 0‖ ≤ η / C := by
      intro k hk
      rw [(hlocal.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
      exact hjet z hzold k hk
    have hh := hcoeff B₁ B₀ z.1 z.2 hsmooth (η / C) (div_pos hη hC).le hjs j hj a b
    simpa only [mul_div_cancel₀ _ hC.ne'] using hh

end PoincareConjecture.SingularTimeAssumptions
