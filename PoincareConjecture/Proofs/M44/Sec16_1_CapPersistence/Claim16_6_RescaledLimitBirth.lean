import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitEquation
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CompactnessFeedBirthSmooth
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CompactnessFeedBirthEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace
local notation "V" => MetricCoefficient 3

noncomputable local instance rescaledLimitBirthCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rescaledLimitBirthCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance rescaledLimitBirthTwoJetNorm : NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance rescaledLimitBirthTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_rescaled_partial_flow_of_compactSmooth
    (g0 : StandardInitialMetric) {T : ℝ} (hT : 0 < T)
    {fseq : ℕ → ℝ × E → V} {b : ℝ × E → V}
    (hconv : CompactSmoothConvergenceOn fseq b atTop (Ioo 0 T ×ˢ univ))
    (hsymm : ∀ p ∈ Ioo 0 T ×ˢ (univ : Set E),
      ∀ᶠ k in atTop, ∀ v w, fseq k p v w = fseq k p w v)
    (hell : ∀ p ∈ Ioo 0 T ×ˢ (univ : Set E), ∃ a : ℝ, 0 < a ∧
      ∀ᶠ k in atTop, ∀ v : E, a * ‖v‖ ^ 2 ≤ fseq k p v v)
    (hevol : ∀ p ∈ Ioo 0 T ×ˢ (univ : Set E), ∀ᶠ k in atTop,
      HasDerivAt (fun t => fseq k (t, p.2))
        (ricciFlowOperator 3 (metricTwoJet (fun x => fseq k (p.1, x)) p.2)) p.1)
    (hbirth : ∀ m : ℕ, ∀ x : E,
      Tendsto (fun k => iteratedFDeriv ℝ m (fun y => fseq k (0, y)) x) atTop
        (𝓝 (iteratedFDeriv ℝ m g0.metric.euclideanCoefficients x)))
    (hmodulus : ∀ m : ℕ, ∀ K : Set E, IsCompact K → ∃ L : ℝ, 0 ≤ L ∧
      ∀ t ∈ Ioo 0 T, ∀ x ∈ K, ∀ᶠ k in atTop,
        ‖iteratedFDeriv ℝ m (fun y => fseq k (t, y)) x -
          iteratedFDeriv ℝ m (fun y => fseq k (0, y)) x‖ ≤ L * t)
    (hcurv : ∀ T0 : ℝ, 0 ≤ T0 → T0 < T →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
        ∀ t ∈ Icc 0 T0, ∀ x ∈ g0.metric.ball 0 R,
          standardJetCurvatureNorm (metricTwoJet (fun y => fseq k (t, y)) x) ≤ K) :
    ∃ S : PartialStandardCapFlow g0, S.lifetime = T ∧
      CompactSmoothConvergenceOn fseq
        (fun p => (S.flow.metric p.1).euclideanCoefficients p.2) atTop
        (Ioo 0 T ×ˢ univ) := by
  let B := birthExtendedCoefficients g0.metric.euclideanCoefficients b
  have hzero : (fun x => B (0, x)) = g0.metric.euclideanCoefficients :=
    birthExtendedCoefficients_zero _ _
  have hBconv : CompactSmoothConvergenceOn fseq B atTop (Ioo 0 T ×ˢ univ) :=
    hconv.congr (fun _ _ _ => rfl) (birthExtendedCoefficients_interior _ _ T)
  have hg0 : ContDiff ℝ ∞ g0.metric.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g0.metric.contDiffAt_euclideanCoefficients
  have hspace : ∀ t ∈ Ico 0 T, ContDiffOn ℝ ∞ (fun x => B (t, x)) univ :=
    birthExtendedCoefficients_spatial_smooth hg0 hconv.smooth
  have hjets : ∀ m : ℕ, ContinuousOn
      (fun p => iteratedFDeriv ℝ m (fun x => B (p.1, x)) p.2) (Ico 0 T ×ˢ univ) :=
    continuousOn_birthExtended_spatialJets hT hg0 hconv hbirth hmodulus
  have hBsymm : ∀ t ∈ Ico 0 T, ∀ x v w, B (t, x) v w = B (t, x) w v := by
    intro t ht x v w
    rcases eq_or_lt_of_le ht.1 with hzero_t | hpos_t
    · subst t
      rw [congrFun hzero x]
      exact g0.metric.symm x v w
    · exact rescaled_limit_coefficients_symmetric hBconv hsymm
        ⟨⟨hpos_t, ht.2⟩, mem_univ x⟩ v w
  have hBpos : ∀ t ∈ Ico 0 T, ∀ x v, v ≠ 0 → 0 < B (t, x) v v := by
    intro t ht x v hv
    rcases eq_or_lt_of_le ht.1 with hzero_t | hpos_t
    · subst t
      rw [congrFun hzero x]
      exact g0.metric.pos x v hv
    · have hp : (t, x) ∈ Ioo 0 T ×ˢ (univ : Set E) :=
        ⟨⟨hpos_t, ht.2⟩, mem_univ x⟩
      obtain ⟨a, ha, he⟩ := hell (t, x) hp
      exact rescaled_limit_coefficients_positive hBconv hp ha he v hv
  have hinv : ∀ p ∈ Ico 0 T ×ˢ (univ : Set E), (B p).IsInvertible := by
    rintro ⟨t, x⟩ ht
    rcases eq_or_lt_of_le ht.1.1 with hzero_t | hpos_t
    · change 0 = t at hzero_t
      subst t
      rw [congrFun hzero x]
      exact g0.metric.inner_isInvertible x
    · have hp : (t, x) ∈ Ioo 0 T ×ˢ (univ : Set E) :=
        ⟨⟨hpos_t, ht.1.2⟩, ht.2⟩
      obtain ⟨a, ha, he⟩ := hell (t, x) hp
      exact CoordinateTransition.isInvertible_of_uniformEllipticity ha
        (rescaled_limit_coefficients_elliptic hBconv hp he)
  have hBevol : ∀ t ∈ Ioo 0 T, ∀ x : E,
      HasDerivAt (fun s => B (s, x))
        (ricciFlowOperator 3 (metricTwoJet (fun y => B (t, y)) x)) t := by
    intro t ht x
    exact hasDerivAt_rescaled_limit_ricci_coefficients hBconv (p := (t, x))
      (fun p hp => hinv p ⟨Ioo_subset_Ico_self hp.1, hp.2⟩) hevol
      ⟨ht, mem_univ x⟩
  have hBsmooth := contDiffOn_ricci_coefficients_birth hT hBconv.smooth hspace hjets hinv hBevol
  have hBwithin : ∀ t ∈ Ico 0 T, ∀ x : E,
      HasDerivWithinAt (fun s => B (s, x))
        (ricciFlowOperator 3 (metricTwoJet (fun y => B (t, y)) x)) (Ico 0 T) t := by
    intro t ht x
    rcases eq_or_lt_of_le ht.1 with hzero_t | hpos_t
    · subst t
      exact hasDerivWithinAt_ricci_coefficients_birth hT hBsmooth.continuousOn hjets hinv
        (fun s hs y _ => hBevol s hs y) (mem_univ x)
    · exact (hBevol t ⟨hpos_t, ht.2⟩ x).hasDerivWithinAt
  obtain ⟨F, hF0, hD0, hcoeff⟩ := exists_rescaled_limit_flow_of_coefficients g0 hT B
    (fun t ht => contDiffOn_univ.mp (hspace t ht)) hBsymm hBpos hBsmooth
    (fun x => congrFun hzero x) hBwithin
  have htwo : ∀ t ∈ Ico 0 T, ∀ x : E,
      Tendsto (fun k => metricTwoJet (fun y => fseq k (t, y)) x) atTop
        (𝓝 (metricTwoJet (F.metric t).euclideanCoefficients x)) := by
    intro t ht x
    rcases eq_or_lt_of_le ht.1 with hzero_t | hpos_t
    · subst t
      rw [hF0]
      exact tendsto_metricTwoJet_of_spatialJets (fun m _ => hbirth m x)
    · rw [hcoeff t ht]
      exact tendsto_metricTwoJet_of_compactSmooth hBconv (p := (t, x))
        ⟨⟨hpos_t, ht.2⟩, mem_univ x⟩
  let S : PartialStandardCapFlow g0 := {
    lifetime := T
    lifetime_pos := hT
    flow := F
    initial_metric := hF0
    initial_connection := hD0
    curvature_locally_bounded := curvature_locally_bounded_of_rescaled_twoJet_limits
      g0 F (fun k t x => metricTwoJet (fun y => fseq k (t, y)) x) htwo hcurv }
  refine ⟨S, rfl, hBconv.congr (fun _ _ _ => rfl) ?_⟩
  intro p hp
  exact congrFun (hcoeff p.1 (Ioo_subset_Ico_self hp.1)) p.2

end PoincareConjecture.M44
