import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeCoefficients
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeMinimality
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeConfinement

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

open Set
open scoped Manifold ContDiff Bundle NNReal Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exists_uniform_uniqueMinimizing_of_candidate_bounds
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    (b : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    {U O : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (htime : ∀ q ∈ U, (lift q).1.val = G.spacetime.timeFunction q)
    (hO : IsOpen O) (hxO : x ∈ O) (hOU : O ⊆ U)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    (hconvex : Convex ℝ S) (hSU : S ⊆ G.gaugeCover.spatial b)
    (hcoord : MapsTo (fun q => (lift q).2.val) O S)
    {N : Set (G.Horizontal x)} (hzero : (0 : G.Horizontal x) ∈ N)
    {η δ C M A : ℝ} (hη : 0 < η) (hηδ : η ≤ δ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hcurv : ∀ q : G.Point, G.spacetime.timeFunction q ∈ Icc (T - δ) T →
      horizontalCurvatureNorm G.leafwise q ≤ C)
    (hcapture : ∀ W ∈ N, ∀ σ ∈ Icc 0 η,
      (W, Real.sqrt σ) ∈ E.domain ∧ E.gamma W (Real.sqrt σ) ∈ O)
    (hspeed : ∀ W ∈ N, ∀ (τ : ℝ) (hτ : τ ∈ Ioc 0 η)
      (hs : (W, Real.sqrt τ) ∈ E.domain), ∀ r ∈ Icc 0 (Real.sqrt τ),
        ‖derivWithin
          (fun v => (lift ((E.path W (Real.sqrt τ) hs (Real.sqrt_pos.mpr hτ.1)).curve
            (v ^ 2))).2.val) (Icc 0 (Real.sqrt τ)) r‖ ≤ M)
    (haction : ∀ W ∈ N, ∀ (τ : ℝ) (hτ : τ ∈ Ioc 0 η)
      (hs : (W, Real.sqrt τ) ∈ E.domain),
        M14BackwardLAction G (E.path W (Real.sqrt τ) hs (Real.sqrt_pos.mpr hτ.1)) ≤
          A * Real.sqrt τ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ η ∧
      ∀ W ∈ N, ∀ τ ∈ Ioc 0 ε, M14UniqueMinimizingBranch G T τ x E W := by
  let d := Real.sqrt η
  have hd : 0 < d := Real.sqrt_pos.mpr hη
  let θ := fun s => (lift (E.gamma 0 s)).1
  have hzero_capture (s : ℝ) (hs : s ∈ Icc 0 d) :
      (0, s) ∈ E.domain ∧ E.gamma 0 s ∈ O := by
    have hsη : s ^ 2 ≤ η :=
      ((sq_le_sq₀ hs.1 (Real.sqrt_nonneg η)).mpr hs.2).trans_eq (Real.sq_sqrt hη.le)
    simpa only [Real.sqrt_sq hs.1] using
      hcapture 0 hzero (s ^ 2) ⟨sq_nonneg s, hsη⟩
  obtain ⟨hθ, hclock⟩ := exponential_gauge_clock_smooth E 0 b lift hlift htime
    (fun s hs => (hzero_capture s hs).1) (fun s hs => hOU (hzero_capture s hs).2)
  obtain ⟨m, hm, K, hpos, hLip⟩ := squareGauge_compact_coefficient_bounds
    hM12 b (lift x).2 hd θ hθ hclock hS hconvex hSU
  let β : ℝ := (K : ℝ) * M ^ 2 / 2 + K + ((K : ℝ) * M) ^ 2 / m
  obtain ⟨e, he, _, hshort⟩ := exists_short_quadratic_interval (β := β) hm hd
  obtain ⟨τC, hτC, _, hconf⟩ := exists_smallTime_action_confinement hM12 x
    (hη.trans_le hηδ) hA hC hcurv hO hxO
  let ε := min η (min τC (e ^ 2))
  have hε : 0 < ε := lt_min hη (lt_min hτC (sq_pos_of_pos he))
  refine ⟨ε, hε, min_le_left _ _, ?_⟩
  intro W hW τ hτ
  have hτη : τ ≤ η := hτ.2.trans (min_le_left _ _)
  have hτC' : τ ≤ τC := hτ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτe : τ ≤ e ^ 2 := hτ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ.1
  have hsD : (W, Real.sqrt τ) ∈ E.domain := (hcapture W hW τ ⟨hτ.1.le, hτη⟩).1
  let p := E.path W (Real.sqrt τ) hsD hs
  have hsq : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ.1.le
  have hpA : M14BackwardLAction G p ≤ A * Real.sqrt ((Real.sqrt τ) ^ 2) := by
    simpa only [Real.sqrt_sq (Real.sqrt_nonneg τ)] using haction W hW τ ⟨hτ.1, hτη⟩ hsD
  have hconfined (q : M14BackwardPath G T 0 ((Real.sqrt τ) ^ 2) x
      (E.gamma W (Real.sqrt τ))) (hq : M14BackwardLAction G q ≤ M14BackwardLAction G p) :
      ∀ r ∈ M14SqrtParameterInterval 0 ((Real.sqrt τ) ^ 2),
        q.curve (r ^ 2) ∈ U ∧ (lift (q.curve (r ^ 2))).2.val ∈ S := by
    have hc := hconf ((Real.sqrt τ) ^ 2)
      (by simpa only [hsq, mem_Ioc] using And.intro hτ.1 hτC')
      _ q (hq.trans hpA)
    intro r hr
    have hqO := hc (squarePath_parameter_mem q hr)
    exact ⟨hOU hqO, hcoord hqO⟩
  have hsub : M14SqrtParameterInterval 0 ((Real.sqrt τ) ^ 2) ⊆ Icc 0 d := by
    intro r hr
    refine ⟨by simpa only [Real.sqrt_zero] using hr.1, ?_⟩
    exact hr.2.trans (Real.sqrt_le_sqrt (by simpa only [hsq] using hτη))
  have hp_speed : ∀ r ∈ M14SqrtParameterInterval 0 ((Real.sqrt τ) ^ 2),
      ‖derivWithin (fun v => (lift (p.curve (v ^ 2))).2.val)
        (M14SqrtParameterInterval 0 ((Real.sqrt τ) ^ 2)) r‖ ≤ M := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, hsq] using
      hspeed W hW τ ⟨hτ.1, hτη⟩ hsD
  have hgap : 0 < m / 4 - β *
      (Real.sqrt ((Real.sqrt τ) ^ 2) - Real.sqrt 0) ^ 2 := by
    simpa only [hsq, Real.sqrt_zero, sub_zero] using
      hshort (Real.sqrt τ) ⟨hs, Real.sqrt_le_iff.mpr ⟨he.le, hτe⟩⟩
  obtain ⟨hmin, hunique⟩ := minimizing_and_unique_of_lowAction_comparison p (by
    intro q hq
    have hc := squarePath_gauge_action_comparison hCoordinates hM12 p q
      (E.path_extension W (Real.sqrt τ) hsD hs) (E.path_euler W (Real.sqrt τ) hsD hs)
      b lift (lift x).2 hU hlift hright (uniqueDiffOn_Icc hd) hsub θ hθ hclock
      hconvex hSU hm K (hconfined p le_rfl) (hconfined q hq) hp_speed hpos hLip hgap
    exact ⟨hc.1, hc.2 hq⟩)
  simpa only [hsq] using uniqueMinimizingBranch_of_selected_path E W hsD hs hmin hunique

end PoincareConjecture.M14
