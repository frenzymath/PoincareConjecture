import PoincareConjecture.Proofs.M47.TerminalSourceJetsCurvature
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CoordinateEvolution
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FiniteOrder.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalSourceJets_backward_norm_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {τ C Z : ℝ} (hτ : 0 < τ) (hC : 0 ≤ C) (hZ : 1 ≤ Z)
    (f : ℝ → V) (hf : ContDiffOn ℝ 1 f (Icc (-τ) 0)) (hinit : ‖f 0‖ ≤ Z)
    (hrate : ∀ t ∈ Ioo (-(τ / 2)) 0, ‖deriv f t‖ ≤ C * (1 + ‖f t‖)) :
    ∀ t ∈ Icc (-(τ / 2)) 0, ‖f t‖ ≤ Z * Real.exp (C * τ) := by
  have hh : ContDiffOn ℝ 1 (fun s : ℝ => f (-s)) (Icc 0 (τ / 2)) := by
    apply hf.comp contDiffOn_id.neg
    intro s hs
    change -s ∈ Icc (-τ) 0
    constructor <;> linarith [hs.1, hs.2]
  have hrate' : ∀ s ∈ Ioo (0 : ℝ) (τ / 2),
      ‖deriv (fun u => f (-u)) s‖ ≤ C * (1 + ‖f (-s)‖) := by
    intro s hs
    have hmem : -s ∈ Ioo (-τ) 0 := by constructor <;> linarith [hs.1, hs.2]
    have hd := (hf.contDiffAt (Icc_mem_nhds hmem.1 hmem.2)).differentiableAt (by norm_num)
    have he : HasDerivAt (fun u => f (-u)) (-deriv f (-s)) s := by
      simpa [Function.comp_def] using hd.hasDerivAt.scomp s (hasDerivAt_id s).neg
    rw [he.deriv, norm_neg]
    exact hrate (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  intro t ht
  have h := M44.norm_le_exp_of_interior_affine_bound (by positivity : (0 : ℝ) < τ / 2)
    hh hC hZ (by simpa using hinit) hrate' (-t)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [neg_neg, sub_zero, show (2 * C) * (τ / 2) = C * τ by ring] using h

theorem terminalSourceJets_spatial (P : RicciFlowCurvatureTheory.{u})
    {τ R H ρ : ℝ} (hτ : 0 < τ) (hH : 0 < H) (hρ : 0 < ρ) (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M],
      ∀ (F : RicciFlow 3 M (Icc (-τ) 0)) (C : TerminalSourceChart (F.metric 0) R),
      (∀ t ∈ Icc (-τ) 0, ∀ y ∈ C.chart '' Metric.ball 0 R,
        (F.connection t).curvatureTensorNorm y ≤ H) →
      ∀ t ∈ Icc (-(τ / 2)) 0, ∀ x ∈ Metric.closedBall 0 ρ, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients C.chart) x‖ ≤ B := by
  classical
  let a := terminalSourceLower H τ
  let b := terminalSourceUpper H τ
  have ha : 0 < a := terminalSourceLower_pos H τ
  have hb : 0 ≤ b := (terminalSourceUpper_pos H τ).le
  have hsub : Icc (-(τ / 2)) 0 ⊆ Icc (-τ) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have htwo : Metric.closedBall (0 : E) ρ ⊆ Metric.closedBall 0 (2 * ρ) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have houter : Metric.closedBall (0 : E) ρ ⊆ Metric.ball 0 (3 * ρ / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have houterR : 3 * ρ / 2 ≤ R := by linarith
  choose K hK hcurv using fun j => terminalSourceJets_curvature P hτ hH hρ hρR hsmall j
  induction m with
  | zero =>
    refine ⟨b, hb, ?_⟩
    intro M _ _ _ _ _ F C hraw t ht x hx j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
    · exact fun v w => (F.metric t).symm _ _ _
    · intro v
      have hnn : 0 ≤ (F.metric t).pullbackCoefficients C.chart x v v := by
        let w := mfderiv (𝓡 3) (𝓡 3) C.chart x v
        change 0 ≤ (F.metric t).inner (C.chart x) w w
        by_cases hw : w = 0
        · simp [hw]
        · exact ((F.metric t).pos _ _ hw).le
      rw [abs_of_nonneg hnn]
      exact (C.closed_bounds hτ hH.le F hρR hsmall hraw (hsub ht) (htwo hx) v).2
  | succ q ih =>
    obtain ⟨B, hB, hlow⟩ := ih
    let A := max B 1
    have hA : 1 ≤ A := le_max_right _ _
    obtain ⟨L, hL, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
      3 q K hK ha hb A hA
    obtain ⟨Z, hZ, hterminal⟩ := CoordinateExponential.exists_uniform_pullback_metric_jet_bound
      3 (q + 1) hρ (by linarith : ρ < 3 * ρ / 2) K hK
    let D := max Z 1
    have hD : 1 ≤ D := le_max_right _ _
    let Bnext := D * Real.exp (L * τ)
    refine ⟨max B Bnext, hB.trans (le_max_left _ _), ?_⟩
    intro M _ _ _ _ _ F C hraw t ht x hx j hj
    rcases Nat.eq_or_lt_of_le hj with rfl | hj
    · apply le_trans _ (le_max_right B Bnext)
      let f := fun s => iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients C.chart) x
      have hxR : x ∈ Metric.ball 0 R := Metric.closedBall_subset_ball hρR (htwo hx)
      have hf : ContDiffOn ℝ 1 f (Icc (-τ) 0) :=
        (M44.contDiffOn_pullback_spatialJet_time (by linarith : -τ < 0) F
          Metric.isOpen_ball C.smooth (q + 1) hxR).of_le (by simp)
      have hinit : ‖f 0‖ ≤ D := by
        apply le_trans _ (le_max_left Z 1)
        apply hterminal (F.metric 0) (F.connection 0) C.chart
          (C.smooth.mono (Metric.ball_subset_ball houterR))
          (fun y hy => C.invertible (Metric.ball_subset_ball houterR hy)) C.normalized
          (fun y hy w => C.gauss (Metric.ball_subset_ball houterR hy) w)
          (fun d _ y hy => hcurv d F C hraw 0 ⟨by linarith, le_rfl⟩ y hy) x hx
      apply terminalSourceJets_backward_norm_bound hτ hL hD f hf hinit ?_ t ht
      intro s hs
      let G := M44.closedSlabInterior (by linarith : -τ < 0) F
      have hrecent : s ∈ Icc (-(τ / 2)) 0 := Ioo_subset_Icc_self hs
      have hsG : s ∈ Ioo (-τ) 0 := ⟨by linarith [hs.1], hs.2⟩
      exact hevol G isOpen_Ioo Metric.isOpen_ball C.smooth
        (fun y hy => C.invertible hy) hsG hxR
        (fun v => (C.closed_bounds hτ hH.le F hρR hsmall hraw (hsub hrecent) (htwo hx) v).1)
        (fun v => (C.closed_bounds hτ hH.le F hρR hsmall hraw (hsub hrecent) (htwo hx) v).2)
        (fun d _ => hcurv d F C hraw s hrecent x (houter hx))
        (fun d hd hdq => (hlow F C hraw s hrecent x hx d hdq).trans
          ((le_max_left B 1).trans (by simpa only [pow_one] using pow_le_pow_right₀ hA hd)))
    · exact (hlow F C hraw t ht x hx j (by omega)).trans (le_max_left _ _)

end PoincareConjecture.M47
