import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.SelectedBallControls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

theorem blowupSequence_tip_ball_scalar_operator_bounds
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    {kappa : ℝ} (A : BlowupAncientKappaIdentification L.limit kappa)
    {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ k, ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k)) ≤ D)
    {s : ℝ} (hs : 0 < s) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let g := E.flow.metric (t (L.subsequence k))
      let Dk := E.flow.connection (t (L.subsequence k))
      ∀ y ∈ g.ball 0 (s / Real.sqrt Q),
        m * Q ≤ Dk.scalarCurvature y ∧ Dk.scalarCurvature y ≤ M * Q ∧
        scalarGradientNorm g Dk y ≤ M * (Q * Real.sqrt Q) ∧
        |Dk.laplacian Dk.scalarCurvature y + 2 * Dk.ricciNormSq y| ≤ M * Q ^ 2 := by
  obtain ⟨m, M, hm, hM, hbound⟩ :=
    blowupSequence_normalized_ball_scalar_operator_bounds P E t x ht hR L A
      (show 0 < D + s + 1 by positivity)
  refine ⟨m, M, hm, hM, ?_⟩
  filter_upwards [hbound] with k hk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let g := E.flow.metric (t (L.subsequence k))
  let G : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric g Q hQ
  let z := x (L.subsequence k)
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have htip : G.edist z 0 ≤ ENNReal.ofReal D := by
    have heq := M13.homothety_edist g G
      (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
      (M13.identity_metricHomothety g Q hQ) 0 z
    change G.edist 0 z = ENNReal.ofReal (Real.sqrt Q) * g.edist 0 z at heq
    have hnorm : (g.edist 0 z).toReal * Real.sqrt Q ≤ D := by
      simpa only [g, z, Q, blowupSequence_scale] using hd (L.subsequence k)
    have hcomm : G.edist z 0 = G.edist 0 z :=
      @edist_comm StandardCapSpace G.toEMetricSpace.toPseudoEMetricSpace z 0
    rw [hcomm, heq,
      ← ENNReal.ofReal_toReal (g.edist_ne_top 0 z),
      ← ENNReal.ofReal_mul hroot.le, mul_comm]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hball := M13.homothety_ball_image g G
    (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) 0 (s / Real.sqrt Q)
  change id '' g.ball 0 (s / Real.sqrt Q) =
    G.ball 0 (Real.sqrt Q * (s / Real.sqrt Q)) at hball
  rw [image_id, mul_div_cancel₀ s hroot.ne'] at hball
  dsimp only
  intro y hy
  have hyG : y ∈ G.ball 0 s := hball ▸ hy
  apply hk y
  change G.edist z y < ENNReal.ofReal (D + s + 1)
  calc
    G.edist z y ≤ G.edist z 0 + G.edist 0 y :=
      @edist_triangle StandardCapSpace G.toEMetricSpace.toPseudoEMetricSpace z 0 y
    _ ≤ ENNReal.ofReal D + ENNReal.ofReal s := add_le_add htip hyG.le
    _ = ENNReal.ofReal (D + s) := (ENNReal.ofReal_add hD hs.le).symm
    _ < ENNReal.ofReal (D + s + 1) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_nonneg hD hs.le)).mpr (by linarith)

end PoincareConjecture.M35.OrdinaryRealization
