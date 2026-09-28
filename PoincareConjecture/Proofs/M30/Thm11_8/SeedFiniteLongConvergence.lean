import PoincareConjecture.Proofs.M30.Thm11_1.ShortControlSupplier
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardGeneralizedConvergence
import PoincareConjecture.Proofs.M30.Thm11_8.BackwardInterval

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem exists_seed_finite_long_convergence_of_short_controls
    (P : M30ControlledBlowupPredecessors.{u})
    (S : GeneralizedBlowupSequence.{u})
    {epsilon C kappa r0 mu : ℝ} {T0 : ℝ≥0∞}
    (H : M30CommonBlowupControls S epsilon C kappa r0 mu)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (Hshort : ShortControlledBlowupHypotheses S kappa r0)
    (hT0 : 0 < T0) :
    ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T < T0 ∧
      Nonempty (GeneralizedBlowupConvergence S (Ioc (-T) 0)) := by
  obtain ⟨d, _hdnonneg, hdpos, hdT0⟩ := ENNReal.lt_iff_exists_real_btwn.mp hT0
  have hd : 0 < d := ENNReal.ofReal_pos.mp hdpos
  let T := min Hshort.backward_time d / 2
  have hT : 0 < T := half_pos (lt_min Hshort.backward_time_pos hd)
  have hTshort : T < Hshort.backward_time := by
    have hle := min_le_left Hshort.backward_time d
    dsimp only [T]
    linarith [lt_min Hshort.backward_time_pos hd]
  have hTd : T < d := by
    have hle := min_le_right Hshort.backward_time d
    dsimp only [T]
    linarith [lt_min Hshort.backward_time_pos hd]
  have hTT0 : ENNReal.ofReal T < T0 :=
    (ENNReal.ofReal_le_ofReal hTd.le).trans_lt hdT0
  obtain ⟨rho, v, hrho, hv, hvolume⟩ :=
    exists_eventually_terminal_volume_lower_bound P.m04 H hbound
  have hcyl : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < ENNReal.ofReal T →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S k A t B eta) := by
    intro t _ht htT
    have htshort : t < Hshort.backward_time :=
      ((ENNReal.ofReal_lt_ofReal_iff hT).mp htT).trans hTshort
    have hI : Icc (-t) 0 ⊆ Icc (-Hshort.backward_time) 0 :=
      Icc_subset_Icc (neg_le_neg htshort.le) le_rfl
    refine ⟨Hshort.curvature_bound, Hshort.curvature_bound_nonneg, ?_⟩
    intro A hA eta heta
    filter_upwards [Hshort.cylinders A hA eta heta] with k hk
    obtain ⟨E⟩ := hk
    exact ⟨{
      embedding := Cylinder.restrict E.embedding hI Subset.rfl
      zero_identity := fun hs x hx => E.zero_identity (hI hs) x hx
      curvature_bound := fun s hs x hx => E.curvature_bound s (hI hs) x hx
      negative_curvature_bound := fun s hs x hx =>
        E.negative_curvature_bound s (hI hs) x hx }⟩
  obtain ⟨G⟩ := exists_backward_generalizedBlowupConvergence
    P.m04.local_derivative_estimates_small withinFlowJetBoundsService.{0, 0}
    withinBilinearFlowService.{0} spatialSliceJetConvergenceService.{0, 0, 0, 0, 0}
    S (ENNReal.ofReal_pos.mpr hT) hrho hv Hshort.balls_compact hcyl hvolume
  exact ⟨T, hT, hTT0, ⟨blowupBackwardInterval_ofReal hT ▸ G⟩⟩

theorem exists_seed_finite_long_convergence_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C kappa r0 mu : ℝ)
        (T0 : ℝ≥0∞),
        epsilon ≤ epsilon0 →
        M30CommonBlowupControls S epsilon C kappa r0 mu →
        0 < T0 →
        (∀ T : ℝ, 0 < T → ENNReal.ofReal T < T0 →
          ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
            Nonempty (M30FiniteHorizonSlab S k A T kappa r0)) →
        ∃ T : ℝ, 0 < T ∧ ENNReal.ofReal T < T0 ∧
          ∃ G : GeneralizedBlowupConvergence S (Ioc (-T) 0),
            ∀ Tplus : ℝ, T < Tplus → ENNReal.ofReal Tplus < T0 →
              ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
                Nonempty (M30FiniteHorizonSlab S (G.subsequence k) A Tplus kappa r0) := by
  obtain ⟨epsilon29, hepsilon29, hepsilon29small, hbound⟩ :=
    exists_boundedDistance_threshold P
  obtain ⟨epsilonShort, hepsilonShort, hshort⟩ := shortControlService P.m04
  refine ⟨min epsilon29 epsilonShort, lt_min hepsilon29 hepsilonShort,
    (min_le_left _ _).trans hepsilon29small, ?_⟩
  intro S epsilon C kappa r0 mu T0 hepsilon H hT0 hslabs
  have hboundS := hbound S epsilon C kappa r0 mu
    (hepsilon.trans (min_le_left _ _)) H
  obtain ⟨phi, hphi, ⟨Hshort⟩⟩ := hshort S epsilon C kappa r0 mu
    (hepsilon.trans (min_le_right _ _)) H hboundS
  obtain ⟨T, hT, hTT0, ⟨G⟩⟩ := exists_seed_finite_long_convergence_of_short_controls P
    (reindexedBlowupSequence S phi hphi) (reindexedCommonBlowupControls H phi hphi)
    (reindexed_boundedDistance hboundS phi hphi) Hshort hT0
  let G0 : GeneralizedBlowupConvergence S (Ioc (-T) 0) := convergenceOfReindexed G
  refine ⟨T, hT, hTT0, G0, ?_⟩
  intro Tplus hTTplus hTplusT0 A hA
  exact G0.subsequence_strictMono.tendsto_atTop.eventually
    (hslabs Tplus (hT.trans hTTplus) hTplusT0 A hA)

end PoincareConjecture.M30
