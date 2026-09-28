import PoincareConjecture.Proofs.M47.LimitFiniteChartBounds
import PoincareConjecture.Proofs.M47.TerminalSourceJetsSpatial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private noncomputable local instance finiteChartJetsDualAdd : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteChartJetsDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteChartJetsBilinAdd :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteChartJetsBilinSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem limitFinite_chart_spatial_jets (P : RicciFlowCurvatureTheory.{u})
    {τ R K ρ a0 b0 Z : ℝ} (hτ : 0 < τ) (hK : 0 < K)
    (hρ : 0 < ρ) (hρR : 2 * ρ < R) (ha0 : 0 < a0) (hb0 : 0 ≤ b0)
    (hZ : 1 ≤ Z) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M],
      ∀ (F : RicciFlow 3 M (Icc (-τ) 0))
        (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞),
      Φ.source = Metric.ball 0 R →
      (∀ t ∈ Icc (-τ) 0, ∀ y ∈ Φ '' Metric.ball 0 R,
        (F.connection t).curvatureTensorNorm y ≤ K) →
      (∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
        a0 * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients Φ x v v ∧
          (F.metric 0).pullbackCoefficients Φ x v v ≤ b0 * ‖v‖ ^ 2) →
      (∀ x ∈ Metric.closedBall 0 ρ, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients Φ) x‖ ≤ Z) →
      ∀ t ∈ Icc (-(τ / 2)) 0, ∀ x ∈ Metric.closedBall 0 ρ, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients Φ) x‖ ≤ B := by
  classical
  let a := a0 * Real.exp (-54 * K * τ)
  let b := b0 * Real.exp (54 * K * τ)
  have ha : 0 < a := mul_pos ha0 (Real.exp_pos _)
  have hb : 0 ≤ b := mul_nonneg hb0 (Real.exp_pos _).le
  have hsub : Icc (-(τ / 2)) 0 ⊆ Icc (-τ) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have htwo : Metric.closedBall (0 : E) ρ ⊆ Metric.closedBall 0 (2 * ρ) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have houter : Metric.closedBall (0 : E) ρ ⊆ Metric.ball 0 (3 * ρ / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  choose D hD hcurv using fun j =>
    limitFinite_chart_curvature (b0 := b0) P hτ hK hρ hρR ha0 j
  induction m with
  | zero =>
    refine ⟨b, hb, ?_⟩
    intro M _ _ _ _ _ F Φ _hsource hraw hterminal _hjet t ht x hx j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
    · exact fun v w => (F.metric t).symm _ _ _
    · intro v
      have hnn : 0 ≤ (F.metric t).pullbackCoefficients Φ x v v := by
        let w := mfderiv (𝓡 3) (𝓡 3) Φ x v
        change 0 ≤ (F.metric t).inner (Φ x) w w
        by_cases hw : w = 0
        · simp [hw]
        · exact ((F.metric t).pos _ _ hw).le
      rw [abs_of_nonneg hnn]
      exact (limitFinite_chart_closed_bounds hτ hK.le hρR F Φ hraw hterminal
        (hsub ht) (htwo hx) v).2
  | succ q ih =>
    obtain ⟨B, hB, hlow⟩ := ih
    let A := max B 1
    have hA : 1 ≤ A := le_max_right _ _
    obtain ⟨L, hL, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
      3 q D hD ha hb A hA
    let Bnext := Z * Real.exp (L * τ)
    refine ⟨max B Bnext, hB.trans (le_max_left _ _), ?_⟩
    intro M _ _ _ _ _ F Φ hsource hraw hterminal hjet t ht x hx j hj
    have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Φ (Metric.ball 0 R) := by
      simpa only [hsource] using Φ.contMDiffOn
    have hinv (y : E) (hy : y ∈ Metric.ball 0 R) :
        (mfderiv (𝓡 3) (𝓡 3) Φ y).IsInvertible :=
      ⟨(Φ.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (hsource.symm ▸ hy)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
    have hlow' := hlow F Φ hsource hraw hterminal
      (fun y hy n hn => hjet y hy n (hn.trans (Nat.le_succ q)))
    rcases Nat.eq_or_lt_of_le hj with rfl | hj
    · apply le_trans _ (le_max_right B Bnext)
      let f := fun s => iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients Φ) x
      have hxR : x ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hρR (htwo hx)
      have hf : ContDiffOn ℝ 1 f (Icc (-τ) 0) :=
        (M44.contDiffOn_pullback_spatialJet_time (by linarith : -τ < 0) F
          Metric.isOpen_ball hsmooth (q + 1) hxR).of_le (by simp)
      apply terminalSourceJets_backward_norm_bound hτ hL hZ f hf
        (hjet x hx (q + 1) le_rfl) ?_ t ht
      intro s hs
      let G := M44.closedSlabInterior (by linarith : -τ < 0) F
      have hrecent : s ∈ Icc (-(τ / 2)) 0 := Ioo_subset_Icc_self hs
      have hsG : s ∈ Ioo (-τ) 0 := ⟨by linarith [hs.1], hs.2⟩
      exact hevol G isOpen_Ioo Metric.isOpen_ball hsmooth hinv hsG hxR
        (fun v => (limitFinite_chart_closed_bounds hτ hK.le hρR F Φ hraw hterminal
          (hsub hrecent) (htwo hx) v).1)
        (fun v => (limitFinite_chart_closed_bounds hτ hK.le hρR F Φ hraw hterminal
          (hsub hrecent) (htwo hx) v).2)
        (fun n _ => hcurv n F Φ hsource hraw hterminal s hrecent x (houter hx))
        (fun n hn hnq => (hlow' s hrecent x hx n hnq).trans
          ((le_max_left B 1).trans (by simpa only [pow_one] using pow_le_pow_right₀ hA hn)))
    · exact (hlow' t ht x hx j (by omega)).trans (le_max_left _ _)

end PoincareConjecture.M47
