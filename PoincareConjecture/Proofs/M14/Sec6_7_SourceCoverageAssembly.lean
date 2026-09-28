import PoincareConjecture.Proofs.M14.Sec6_7_AnalyticData
import PoincareConjecture.Proofs.M14.Sec6_7_ZeroTimeIntegral
import PoincareConjecture.Proofs.M14.Thm8_1_TerminalLowerBound

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem reducedVolumeSourceCoverageData_of_smallTimeCoverage
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hsmall : M14SmallTimeCoverageStatement G) :
    Nonempty (M14ReducedVolumeSourceCoverageData G) := by
  classical
  refine ⟨{
    zero_time_limit := ?_
    disjoint_image_additivity := ?_
    terminal_W_lower_bound := ?_ }⟩
  · intro T x E B δ hδ hwindow hcompact _ hexhaust K hK hcurv
    obtain ⟨τ₀, hτ₀, hτ₀δ, hbase⟩ := hsmall T x E (B 0) (K 0) δ hδ hwindow
      (hcompact 0) (hK 0).1 (hK 0).2.1 (hK 0).2.2 hcurv
    let H := fun τ hτ hτlt => Classical.choose (hbase τ hτ hτlt)
    obtain ⟨b, hb⟩ := exists_orthonormal_horizontalBasis G x
    let A := fun τ hτ hτlt =>
      reducedVolumeAnalyticDataWithBasis hCoordinates hM04 hM12 E (H τ hτ hτlt) b hb
    have hcoverage (k : ℕ) : ∃ η : ℝ, 0 < η ∧ η ≤ τ₀ ∧
        ∀ (τ : ℝ) (hτ : 0 < τ) (hτlt : τ < τ₀), τ < η →
          B k ⊆ (H τ hτ hτlt).carrier ∧
            ∀ Z ∈ B k, ∀ s ∈ Icc 0 τ, E.gamma Z (Real.sqrt s) ∈ K k := by
      obtain ⟨η, hη, _, hk⟩ := hsmall T x E (B k) (K k) δ hδ hwindow
        (hcompact k) (hK k).1 (hK k).2.1 (hK k).2.2 hcurv
      refine ⟨min η τ₀, lt_min hη hτ₀, min_le_right _ _, ?_⟩
      intro τ hτ hτlt hτη
      obtain ⟨Hk, hBk, hcapture⟩ := hk τ hτ (hτη.trans_le (min_le_left _ _))
      refine ⟨?_, hcapture⟩
      intro Z hZ
      exact ((H τ hτ hτlt).carrier_exact Z).mpr ((Hk.carrier_exact Z).mp (hBk hZ))
    have hcover (Z : G.Horizontal x) : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∃ hτ : 0 < τ, ∃ hτlt : τ < τ₀, Z ∈ (H τ hτ hτlt).carrier := by
      obtain ⟨k, hZ⟩ := hexhaust Z
      obtain ⟨η, hη, hητ₀, hk⟩ := hcoverage k
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hη)] with τ hτ hτη
      have hτlt : τ < τ₀ := hτη.trans_le hητ₀
      exact ⟨hτ, hτlt, (hk τ hτ hτlt hτη).1 hZ⟩
    refine ⟨τ₀, hτ₀, hτ₀δ, H, A, ?_, hcoverage, ?_⟩
    · intro τ hτ hτlt
      exact analyticCarrier_eq_stableVolume (H τ hτ hτlt) (A τ hτ hτlt)
    · have hlim := tendsto_reducedVolume_of_eventual_stability hCoordinates hM04 hM12 E b hb
        hτ₀ H hcover
      apply hlim.congr'
      apply Eventually.of_forall
      intro τ
      dsimp only
      split_ifs with hτ hτlt
      · exact (analyticCarrier_eq_stableVolume (H τ hτ hτlt) (A τ hτ hτlt)).symm
      · rfl
      · rfl
  · intro T τ x E H A
    exact disjointImageAdditivity H A
  · intro T τmax x E τ₀ _ _ H₀ A₀ W hopen hne hm hW l₀ V _ _ hl hV
    exact terminal_lower_bound_and_earlier H₀ A₀
      (fun _ Hσ => reducedVolumeAnalyticData hCoordinates hM04 hM12 E Hσ)
      hW hne hopen hm hl hV

end PoincareConjecture.M14
