import PoincareConjecture.Proofs.M30.Thm11_8.FiniteLeftCoefficients
import PoincareConjecture.Proofs.M30.Mathlib.SameSequenceClosedCompactness











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 1800000 in



theorem tendsto_original_stage_jets_through_finite_left
    {S : GeneralizedBlowupSequence.{u}} {T tau : ℝ} (hT : 0 < T)
    (hTtau : T < tau)
    (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
    (Y : TopologicalSpace.Opens G.limit.carrier.carrier) (N : ℕ)
    (P : ℕ → RicciFlow 3 Y (Icc (-tau) 0))
    (hstage : ∀ k, (Y : Set G.limit.carrier.carrier) ⊆
      G.exhaustion.space (k + N))
    (hmetric : ∀ k s (_hs : s ∈ Icc (-tau) 0)
        (hsG : s ∈ Icc (-G.exhaustion.time (k + N)) 0)
        (x : Y) (v w : TangentSpace (𝓡 3) x),
      ((P k).metric s).inner x v w =
        (G.embedding (k + N)).pullbackInner s hsG x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Y → G.limit.carrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Y → G.limit.carrier.carrier) x w))
    (hcurv : ∀ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ k t,
      t ∈ Icc (-tau) 0 → ∀ x : Y,
        ((P k).connection t).curvatureDerivativeNorm m x ≤ D)
    (Fbar : RicciFlow 3 G.limit.carrier.carrier (Icc (-T) 0))
    (hFbar : ∀ t ∈ Ioc (-T) 0, Fbar.metric t = G.limit.flow.metric t)
    (q : G.limit.carrier.carrier) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : IsOpen U) (hUc : U ⊆ (extChartAt (𝓡 3) q).target)
    (psi : EuclideanSpace ℝ (Fin 3) → Y)
    (hpsi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ psi U)
    (hpsival : ∀ x ∈ U, (psi x).val = (extChartAt (𝓡 3) q).symm x)
    (hi : ∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) psi x).IsInvertible)
    (x0 : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x0 r ⊆ U) :
    let Omega := Icc (-T) 0 ×ˢ Metric.closedBall x0 r
    ∀ m : ℕ, TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun z => ((P k).metric z.1).pullbackCoefficients psi z.2) Omega)
      (iteratedFDerivWithin ℝ m
        (fun z => (Fbar.metric z.1).pullbackCoefficients
          (extChartAt (𝓡 3) q).symm z.2) Omega) atTop Omega := by
  classical
  intro Omega
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let f := fun k (z : ℝ × E) => ((P k).metric z.1).pullbackCoefficients psi z.2
  let g := fun z : ℝ × E =>
    (Fbar.metric z.1).pullbackCoefficients (extChartAt (𝓡 3) q).symm z.2
  let Wide := Icc (-tau) 0 ×ˢ U
  have htau : 0 < tau := hT.trans hTtau
  have hOmegaWide : Omega ⊆ Wide := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, hball hz.2⟩
  have hcompact : IsCompact Omega := isCompact_Icc.prod (isCompact_closedBall x0 r)
  have hconvex : Convex ℝ Omega := (convex_Icc (-T) 0).prod (convex_closedBall x0 r)
  have hinterior : interior Omega = Ioo (-T) 0 ×ˢ Metric.ball x0 r := by
    simp only [Omega, interior_prod_eq, interior_Icc, interior_closedBall x0 hr.ne']
  have hne : (interior Omega).Nonempty := by
    rw [hinterior]
    exact ⟨(-T / 2, x0), ⟨by linarith, by linarith⟩, Metric.mem_ball_self hr⟩
  have hdiff : UniqueDiffOn ℝ Omega := uniqueDiffOn_convex hconvex hne
  have hdiffWide : UniqueDiffOn ℝ Wide :=
    (uniqueDiffOn_Icc (by linarith : -tau < 0)).prod hU.uniqueDiffOn
  have hsourceWide (k : ℕ) : ContDiffOn ℝ ∞ (f k) Wide :=
    (P k).smooth.contDiffOn_spacetime_pullbackCoefficients_within hU hpsi
  have htarget : ContDiffOn ℝ ∞ g Omega := by
    have hs := Fbar.smooth.contDiffOn_spacetime_pullbackCoefficients_within hU
      ((contMDiffOn_extChartAt_symm (n := ∞) q).mono hUc)
    exact hs.mono fun z hz => ⟨hz.1, hball hz.2⟩
  have hdata := generalized_stage_coefficients_and_closed_bounds hT hTtau G
    Y N P hstage hmetric hcurv q U hU hUc psi hpsi hpsival hi
  obtain ⟨_, _, _, _, _, hb⟩ := hdata.2.2 (Metric.closedBall x0 r)
    (isCompact_closedBall x0 r) hball
  have hbound (K : Set (ℝ × E)) (_hK : IsCompact K) (hKO : K ⊆ Omega) (m : ℕ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
        ‖iteratedFDerivWithin ℝ m (f k) Omega z‖ ≤ B := by
    obtain ⟨B, hB, hBk⟩ := hb m
    refine ⟨B, hB, hBk.mono ?_⟩
    intro k hk z hz
    rw [iteratedFDerivWithin_subset hOmegaWide hdiff hdiffWide
      ((hsourceWide k).of_le (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)) (hKO hz)]
    exact hk z ⟨(hOmegaWide (hKO hz)).1, (hKO hz).2⟩
  have hpoint : ∀ z ∈ interior Omega, Tendsto (fun k => f k z) atTop (𝓝 (g z)) := by
    intro z hz
    rw [hinterior] at hz
    have ht : z.1 ∈ Ioc (-T) 0 := ⟨hz.1.1, hz.1.2.le⟩
    have hx : z.2 ∈ U := hball (Metric.ball_subset_closedBall hz.2)
    have hj := (hdata.2.1 0 {z} isCompact_singleton
      (singleton_subset_iff.mpr ⟨ht, hx⟩)).tendsto_at (mem_singleton z)
    have hc := (continuous_eval_const (0 : Fin 0 → E)).continuousAt.tendsto.comp hj
    simpa only [f, g, Function.comp_def, hFbar z.1 ht, iteratedFDeriv_zero_apply] using! hc
  obtain ⟨B, hB, hBg, hjet⟩ :=
    exists_smooth_limit_on_closed_convex_of_eventually_of_pointwise
      hcompact.isClosed hconvex hne f g
      (Eventually.of_forall fun k => (hsourceWide k).mono hOmegaWide) hbound hpoint
  have hclosure : closure (interior Omega) = Omega :=
    (hconvex.closure_interior_eq_closure_of_nonempty_interior hne).trans
      hcompact.isClosed.closure_eq
  have hBgClosed : EqOn B g Omega := hBg.of_subset_closure hB.continuousOn
    htarget.continuousOn interior_subset hclosure.symm.subset
  intro m
  exact (hjet m Omega hcompact (Subset.refl Omega)).congr_right
    (hBgClosed.iteratedFDerivWithin (𝕜 := ℝ) m)

end PoincareConjecture.M30
