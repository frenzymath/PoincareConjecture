import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.AnalyticCapBounds
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.SelectedCoreVolume
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.SelectedTipBallControls
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.TwoCollars
import PoincareConjecture.Proofs.M35.RawFlow.BlowupTimes











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness




theorem blowupSequence_caps_of_radial_collars
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    {kappa : ℝ} (A : BlowupAncientKappaIdentification L.limit kappa)
    {epsilon D s F : ℝ} (he : 0 < epsilon) (hehalf : epsilon < 1 / 2)
    (hD : 0 ≤ D)
    (hd : ∀ k, ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k)) ≤ D)
    (hs : 0 < s)
    (hcollars : ∀ᶠ k in atTop,
      ∃ N : RadialCapCollars E (t (L.subsequence k)) (ht _) epsilon,
        radialArclength (E.flow.metric (t (L.subsequence k))) ‖x (L.subsequence k)‖ <
          N.a - N.b * epsilon⁻¹ ∧
        (N.a + N.b * epsilon⁻¹) *
          Real.sqrt ((blowupSequence P E t x ht hR).scale (L.subsequence k)) ≤ s ∧
        intrinsicWarpingRadius (E.flow.metric (t (L.subsequence k)))
          (E.rotation_invariant _ (ht _)) (E.complete _ (ht _)) N.a *
            Real.sqrt ((blowupSequence P E t x ht hR).scale (L.subsequence k)) ≤ F) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ k in atTop, ∀ C ≥ C₀,
      Nonempty (StandardCapNeighborhood E.atlas E.flow
        (t (L.subsequence k)) epsilon C (x (L.subsequence k))) := by
  obtain ⟨m, M, hm, hM, hball⟩ :=
    blowupSequence_tip_ball_scalar_operator_bounds P E t x ht hR L A hD hd hs
  obtain ⟨Ca, hCa, hanalytic⟩ := exists_radial_cap_analytic_constant hm hM hs
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ (k : ℕ) : 0 < Q k :=
    (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  have hQtop : Tendsto Q atTop atTop := by
    simpa only [Q, blowupSequence_scale, Function.comp_def] using
      hR.comp L.subsequence_strictMono.tendsto_atTop
  have htone : Tendsto (t ∘ L.subsequence) atTop (𝓝 1) := by
    simpa only [E.lifetime_one] using
      (E.flow.base.tendsto_time_of_scalar_diverges t x ht hR).comp
        L.subsequence_strictMono.tendsto_atTop
  obtain ⟨Cv, _hCv, hcorevolume⟩ := exists_selected_core_volume_constant P E
    (t ∘ L.subsequence) Q (fun k => ht _) hQ htone hQtop (3 * F)
  refine ⟨max Ca Cv, hCa.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hball, hcorevolume, hcollars] with k hk hcore hkcollars
  obtain ⟨N, hcenter, hsize, horbit⟩ := hkcollars
  intro C hC
  have hCaC : Ca ≤ C := (le_max_left Ca Cv).trans hC
  have hCvC : Cv ≤ C := (le_max_right Ca Cv).trans hC
  have hCpos : 0 < C := hCa.trans_le hCaC
  let g := E.flow.metric (t (L.subsequence k))
  let Dk := E.flow.connection (t (L.subsequence k))
  let R := N.a + N.b * epsilon⁻¹
  have hRpos : 0 < R := add_pos N.a_pos (mul_pos N.b_pos (inv_pos.mpr he))
  have hRbound : R ≤ s / Real.sqrt (Q k) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr (hQ k))).mpr hsize
  have hbounds (y : StandardCapSpace) (hy : y ∈ g.ball 0 R) :
      m * Q k ≤ Dk.scalarCurvature y ∧ Dk.scalarCurvature y ≤ M * Q k ∧
      scalarGradientNorm g Dk y ≤ M * (Q k * Real.sqrt (Q k)) ∧
      |Dk.laplacian Dk.scalarCurvature y + 2 * Dk.ricciNormSq y| ≤ M * Q k ^ 2 :=
    hk y (hy.trans_le (ENNReal.ofReal_le_ofReal hRbound))
  obtain ⟨hratio, hdiameter, hvolume, hgradient, hevolution⟩ :=
    hanalytic C hCaC g Dk (Q k) R (hQ k) hRpos hRbound hbounds
  refine ⟨radialCapNeighborhood P E (t (L.subsequence k)) (ht _)
    (x (L.subsequence k)) N.q N.a N.b N.b' N.Q N.Q' epsilon C
    N.b_pos N.b'_pos N.Q_pos N.Q'_pos he hehalf hCpos N.unit N.unit'
    N.inner_pos N.boundary_inner_pos N.speed hcenter N.scalar N.boundary_scalar
    N.comparison N.boundary_comparison N.far N.width hratio hdiameter hvolume
    ?_ hgradient hevolution⟩
  intro y _hy r hr hrbound hrscale
  apply hcore C hCvC y r hr _ hrscale
  have h := mul_le_mul_of_nonneg_right hrbound (Real.sqrt_nonneg (Q k))
  nlinarith only [h, horbit]

end PoincareConjecture.M35.OrdinaryRealization
