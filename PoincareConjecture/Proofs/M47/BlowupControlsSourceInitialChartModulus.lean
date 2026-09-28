import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialChartJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem source_initial_chart_time_modulus (P : RicciFlowCurvatureTheory.{u})
    {tau R K rho a b : ℝ} (htau : 0 < tau) (hK : 0 < K)
    (hrho : 0 < rho) (hrhoR : 2 * rho < R) (ha : 0 < a) (hb : 0 ≤ b)
    (Z : ℕ → ℝ) (j : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
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
      (∀ k ≤ j, ‖iteratedFDeriv ℝ k ((F.metric 0).pullbackCoefficients Phi) x‖ ≤ Z k) →
      ∀ s ∈ Icc (-(tau / 2)) 0, ∀ t ∈ Icc (-(tau / 2)) 0,
        ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients Phi) x -
          iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients Phi) x‖ ≤ L * |t - s| := by
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
  cases j with
  | zero =>
    refine ⟨2 * (3 : ℝ) ^ 3 * K * upper, by positivity, ?_⟩
    intro M _ _ _ _ _ F Phi hsource hraw hterminal x hx _hjets s hs t ht
    have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi (Metric.ball 0 (2 * rho)) := by
      apply Phi.contMDiffOn.mono
      rw [hsource]
      exact Metric.ball_subset_ball hrhoR.le
    have hmetric : ∀ v ∈ Icc (-tau) 0, ∀ y ∈ Metric.ball (0 : E) (2 * rho), ∀ w,
        (F.metric v).pullbackCoefficients Phi y w w ≤ upper * ‖w‖ ^ 2 := by
      intro v hv y hy w
      exact (source_initial_chart_closed_bounds htau hK.le hrhoR F Phi hraw
        hterminal hv (Metric.ball_subset_closedBall hy) w).2
    have hcurv : ∀ v ∈ Icc (-tau) 0, ∀ y ∈ Metric.ball (0 : E) (2 * rho),
        (F.connection v).curvatureTensorNorm (Phi y) ≤ K := by
      intro v hv y hy
      exact hraw v hv _ ⟨y, Metric.ball_subset_ball hrhoR.le hy, rfl⟩
    have h := M44.closed_metric_zeroth_jet_estimates
      (by linarith only [htau] : -tau < 0) hupper hK.le F Metric.isOpen_ball
      hsmooth hmetric hcurv x (Metric.closedBall_subset_ball (by linarith only [hrho]) hx)
    exact h.2 s (hsub hs) t (hsub ht)
  | succ q =>
    choose Kjet hKjet hcurvature using
      fun k => source_initial_chart_curvature P (b := b) htau hK hrho hrhoR ha k
    obtain ⟨B, hB, hbounded⟩ := source_initial_chart_jets P htau hK hrho hrhoR ha hb Z (q + 1)
    let A := max B 1
    have hA : 1 ≤ A := le_max_right _ _
    obtain ⟨C, hC, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
      3 q Kjet hKjet hlower hupper A hA
    refine ⟨C * (1 + B), by positivity, ?_⟩
    intro M _ _ _ _ _ F Phi hsource hraw hterminal x hx hjets
    have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi (Metric.ball 0 R) := by
      simpa only [hsource] using Phi.contMDiffOn
    have hinvert : ∀ y ∈ Metric.ball 0 R,
        (mfderiv (𝓡 3) (𝓡 3) Phi y).IsInvertible := by
      intro y hy
      exact ⟨(Phi.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (hsource.symm ▸ hy)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
    have hnorm := hbounded F Phi hsource hraw hterminal x hx hjets
    let f := fun t => iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients Phi) x
    have hxR : x ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hrhoR (htwo hx)
    have hf : ContDiffOn ℝ 1 f (Icc (-tau) 0) :=
      (M44.contDiffOn_pullback_spatialJet_time (by linarith only [htau] : -tau < 0)
        F Metric.isOpen_ball hsmooth (q + 1) hxR).of_le (by simp)
    apply M44.norm_sub_le_of_interior_deriv_bound
      (by linarith only [htau] : -(tau / 2) < 0) (hf.mono hsub)
    intro t ht
    let G := M44.closedSlabInterior (by linarith only [htau] : -tau < 0) F
    have hrecent : t ∈ Icc (-(tau / 2)) 0 := Ioo_subset_Icc_self ht
    have htG : t ∈ Ioo (-tau) 0 := ⟨by linarith only [ht.1, htau], ht.2⟩
    have hrate := hevol G isOpen_Ioo Metric.isOpen_ball hsmooth hinvert htG hxR
      (fun v => (source_initial_chart_closed_bounds htau hK.le hrhoR F Phi hraw
        hterminal (hsub hrecent) (htwo hx) v).1)
      (fun v => (source_initial_chart_closed_bounds htau hK.le hrhoR F Phi hraw
        hterminal (hsub hrecent) (htwo hx) v).2)
      (fun k _ => hcurvature k F Phi hsource hraw hterminal t hrecent x (houter hx))
      (fun k hk hkq => (hnorm t hrecent k (hkq.trans (Nat.le_succ q))).trans
        ((le_max_left B 1).trans
          (by simpa only [pow_one] using pow_le_pow_right₀ hA hk)))
    exact hrate.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (hnorm t hrecent (q + 1) le_rfl)) hC)

end PoincareConjecture.M47
