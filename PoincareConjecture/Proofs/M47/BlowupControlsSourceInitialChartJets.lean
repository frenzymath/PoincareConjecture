import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialChartCurvature
import PoincareConjecture.Proofs.M47.TerminalSourceJetsSpatial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem source_initial_chart_jets (P : RicciFlowCurvatureTheory.{u})
    {tau R K rho a b : ℝ} (htau : 0 < tau) (hK : 0 < K)
    (hrho : 0 < rho) (hrhoR : 2 * rho < R) (ha : 0 < a) (hb : 0 ≤ b)
    (Z : ℕ → ℝ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M],
      ∀ (F : RicciFlow 3 M (Icc (-tau) 0))
        (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞),
      Phi.source = Metric.ball 0 R →
      (∀ s ∈ Icc (-tau) 0, ∀ y ∈ Phi '' Metric.ball 0 R,
        (F.connection s).curvatureTensorNorm y ≤ K) →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
        a * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients Phi x v v ∧
          (F.metric 0).pullbackCoefficients Phi x v v ≤ b * ‖v‖ ^ 2) →
      ∀ x ∈ Metric.closedBall (0 : E) rho,
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients Phi) x‖ ≤ Z j) →
      ∀ s ∈ Icc (-(tau / 2)) 0, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients Phi) x‖ ≤ B := by
  classical
  let lower := a * Real.exp (-54 * K * tau)
  let upper := b * Real.exp (54 * K * tau)
  have hlower : 0 < lower := mul_pos ha (Real.exp_pos _)
  have hupper : 0 ≤ upper := mul_nonneg hb (Real.exp_pos _).le
  have hsub : Icc (-(tau / 2)) 0 ⊆ Icc (-tau) 0 := by
    intro s hs
    exact ⟨by linarith only [hs.1, htau], hs.2⟩
  have htwo : Metric.closedBall (0 : E) rho ⊆ Metric.closedBall 0 (2 * rho) :=
    Metric.closedBall_subset_closedBall (by linarith only [hrho])
  have houter : Metric.closedBall (0 : E) rho ⊆ Metric.ball 0 (3 * rho / 2) :=
    Metric.closedBall_subset_ball (by linarith only [hrho])
  choose Kjet hKjet hcurvature using
    fun j => source_initial_chart_curvature P (b := b) htau hK hrho hrhoR ha j
  induction m with
  | zero =>
    refine ⟨upper, hupper, ?_⟩
    intro M _ _ _ _ _ F Phi hsource hraw hterminal x hx _hjets s hs j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hupper
    · exact fun v w => (F.metric s).symm _ _ _
    · intro v
      have hnn : 0 ≤ (F.metric s).pullbackCoefficients Phi x v v := by
        let w := mfderiv (𝓡 3) (𝓡 3) Phi x v
        change 0 ≤ (F.metric s).inner (Phi x) w w
        by_cases hw : w = 0
        · simp only [hw, map_zero, le_refl]
        · exact ((F.metric s).pos _ _ hw).le
      rw [abs_of_nonneg hnn]
      exact (source_initial_chart_closed_bounds htau hK.le hrhoR F Phi hraw
        hterminal (hsub hs) (htwo hx) v).2
  | succ q ih =>
    obtain ⟨B, hB, hlow⟩ := ih
    let A := max B 1
    have hA : 1 ≤ A := le_max_right _ _
    obtain ⟨L, hL, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
      3 q Kjet hKjet hlower hupper A hA
    let D := max (Z (q + 1)) 1
    have hD : 1 ≤ D := le_max_right _ _
    let Bnext := D * Real.exp (L * tau)
    refine ⟨max B Bnext, hB.trans (le_max_left _ _), ?_⟩
    intro M _ _ _ _ _ F Phi hsource hraw hterminal x hx hjets s hs j hj
    have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi (Metric.ball 0 R) := by
      simpa only [hsource] using Phi.contMDiffOn
    have hinvert : ∀ y ∈ Metric.ball 0 R,
        (mfderiv (𝓡 3) (𝓡 3) Phi y).IsInvertible := by
      intro y hy
      exact ⟨(Phi.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (hsource.symm ▸ hy)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
    have hlowAt := hlow F Phi hsource hraw hterminal x hx
      (fun d hd => hjets d (hd.trans (Nat.le_succ q)))
    rcases Nat.eq_or_lt_of_le hj with rfl | hj
    · apply le_trans _ (le_max_right B Bnext)
      let f := fun t => iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients Phi) x
      have hxR : x ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hrhoR (htwo hx)
      have hf : ContDiffOn ℝ 1 f (Icc (-tau) 0) :=
        (M44.contDiffOn_pullback_spatialJet_time (by linarith only [htau] : -tau < 0)
          F Metric.isOpen_ball hsmooth (q + 1) hxR).of_le (by simp)
      have hinit : ‖f 0‖ ≤ D := (hjets (q + 1) le_rfl).trans (le_max_left _ _)
      apply terminalSourceJets_backward_norm_bound htau hL hD f hf hinit ?_ s hs
      intro t ht
      let G := M44.closedSlabInterior (by linarith only [htau] : -tau < 0) F
      have hrecent : t ∈ Icc (-(tau / 2)) 0 := Ioo_subset_Icc_self ht
      have htG : t ∈ Ioo (-tau) 0 := ⟨by linarith only [ht.1, htau], ht.2⟩
      exact hevol G isOpen_Ioo Metric.isOpen_ball hsmooth hinvert htG hxR
        (fun v => (source_initial_chart_closed_bounds htau hK.le hrhoR F Phi hraw
          hterminal (hsub hrecent) (htwo hx) v).1)
        (fun v => (source_initial_chart_closed_bounds htau hK.le hrhoR F Phi hraw
          hterminal (hsub hrecent) (htwo hx) v).2)
        (fun d _ => hcurvature d F Phi hsource hraw hterminal t hrecent x (houter hx))
        (fun d hd hdq => (hlowAt t hrecent d hdq).trans
          ((le_max_left B 1).trans
            (by simpa only [pow_one] using pow_le_pow_right₀ hA hd)))
    · exact (hlowAt s hs j (by omega)).trans (le_max_left _ _)

end PoincareConjecture.M47
