import PoincareConjecture.Proofs.M30.Thm11_8.UniformPrefixFromFiniteLimit
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSlabContinuation
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteSlabControlled
import PoincareConjecture.Proofs.M30.Thm11_8.SeedFiniteLongConvergence











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold




theorem exists_uniform_left_cylinders_of_bounded_finite_limit
    (hC : RicciFlowCurvatureTheory.{u})
    {S : GeneralizedBlowupSequence.{u}} {T Tplus : ℝ}
    {epsilon C kappa r0 mu : ℝ}
    (H : M30CommonBlowupControls S epsilon C kappa r0 mu)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (hT : 0 < T) (hTTplus : T < Tplus)
    (hslabs : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      Nonempty (M30FiniteHorizonSlab S k A Tplus kappa r0))
    (hscalar : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Ioc (-T) 0, ∀ x,
      (G.limit.flow.connection s).scalarCurvature x ≤ B) :
    ∃ delta : ℝ, 0 < delta ∧ T + delta < Tplus ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (NoncollapsedControlledBlowupCylinder
            (reindexedBlowupSequence S G.subsequence G.subsequence_strictMono)
            k A (T + delta) B eta kappa r0) := by
  obtain ⟨D, hD, hprefix⟩ := eventually_uniform_prefix_scalar_of_finite_limit
    G hT hTTplus hslabs hscalar
  let H' := reindexedCommonBlowupControls H G.subsequence G.subsequence_strictMono
  let delta := min (T / 4)
    (min ((Tplus - T) / 4) (1 / (32 * H'.analytic_constant * D)))
  have hdelta : 0 < delta := by
    apply lt_min (div_pos hT (by norm_num))
    apply lt_min (div_pos (sub_pos.mpr hTTplus) (by norm_num))
    apply one_div_pos.mpr
    have hDpos : 0 < D := by linarith
    positivity [H'.analytic_constant_pos]
  have hbuffer : T + delta < Tplus := by
    have hle : delta ≤ (Tplus - T) / 4 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  refine ⟨delta, hdelta, hbuffer, 26 * D, by linarith, ?_⟩
  intro A hA eta heta
  obtain ⟨_hdelta, hbuffer', hfamily⟩ :=
    eventually_finiteSlab_bounds_of_uniform_prefix_scalar hC H'
      A T Tplus D hA hT hTTplus hD (hprefix A hA)
  filter_upwards [hfamily eta heta] with k hk
  obtain ⟨e, hcurvature, hdefect⟩ := hk
  exact ⟨noncollapsedControlledCylinderOfFiniteHorizonSlab e hbuffer'
    (fun s hs x _hx => hcurvature s hs x)
    (fun s hs x _hx => hdefect s hs x)⟩




theorem exists_larger_finite_convergence_of_scalar_bound
    (P : M30ControlledBlowupPredecessors.{u})
    {S : GeneralizedBlowupSequence.{u}} {T : ℝ} {T0 : ℝ≥0∞}
    {epsilon C kappa r0 mu : ℝ}
    (H : M30LongBlowupControls S epsilon C kappa r0 mu T0)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (hT : 0 < T) (hTT0 : ENNReal.ofReal T < T0)
    (hscalar : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Ioc (-T) 0, ∀ x,
      (G.limit.flow.connection s).scalarCurvature x ≤ B) :
    ∃ T' : ℝ, T < T' ∧ ENNReal.ofReal T' < T0 ∧
      Nonempty (GeneralizedBlowupConvergence S (Ioc (-T') 0)) := by
  obtain ⟨Tplus, _hTplusNonneg, hTTplus, hTplusT0⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp hTT0
  have hTplus : 0 < Tplus := ENNReal.ofReal_pos.mp (lt_of_le_of_lt
    (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal T) hTTplus)
  have hTTplus' : T < Tplus := (ENNReal.ofReal_lt_ofReal_iff hTplus).mp hTTplus
  obtain ⟨delta, hdelta, hbuffer, B, hB, hfamily⟩ :=
    exists_uniform_left_cylinders_of_bounded_finite_limit P.m04
      H.toM30CommonBlowupControls G hT hTTplus'
      (H.slabs Tplus (hT.trans hTTplus') hTplusT0) hscalar
  let S' := reindexedBlowupSequence S G.subsequence G.subsequence_strictMono
  let H' := reindexedCommonBlowupControls H.toM30CommonBlowupControls
    G.subsequence G.subsequence_strictMono
  obtain ⟨rho, v, hrho, hv, hvolume⟩ :=
    exists_eventually_terminal_volume_lower_bound P.m04 H'
      (reindexed_boundedDistance hbound G.subsequence G.subsequence_strictMono)
  have hT' : 0 < T + delta := add_pos hT hdelta
  have hcyl : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < ENNReal.ofReal (T + delta) →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop, Nonempty (ControlledBlowupCylinder S' k A t B eta) := by
    intro t _ht ht
    have ht' : t < T + delta := (ENNReal.ofReal_lt_ofReal_iff hT').mp ht
    have hI : Icc (-t) 0 ⊆ Icc (-(T + delta)) 0 :=
      Icc_subset_Icc (neg_le_neg ht'.le) le_rfl
    refine ⟨B, hB, ?_⟩
    intro A hA eta heta
    filter_upwards [hfamily A hA eta heta] with k hk
    obtain ⟨E⟩ := hk
    exact ⟨{
      embedding := Cylinder.restrict E.toControlledBlowupCylinder.embedding hI Subset.rfl
      zero_identity := fun hs x hx => E.zero_identity (hI hs) x hx
      curvature_bound := fun s hs x hx => E.curvature_bound s (hI hs) x hx
      negative_curvature_bound := fun s hs x hx =>
        E.negative_curvature_bound s (hI hs) x hx }⟩
  obtain ⟨G'⟩ := exists_backward_generalizedBlowupConvergence
    P.m04.local_derivative_estimates_small withinFlowJetBoundsService.{0, 0}
    withinBilinearFlowService.{0} spatialSliceJetConvergenceService.{0, 0, 0, 0, 0}
    S' (ENNReal.ofReal_pos.mpr hT') hrho hv H'.balls_compact hcyl hvolume
  refine ⟨T + delta, by linarith,
    (ENNReal.ofReal_le_ofReal hbuffer.le).trans_lt hTplusT0, ?_⟩
  exact ⟨convergenceOfReindexed (blowupBackwardInterval_ofReal hT' ▸ G')⟩

end PoincareConjecture.M30
