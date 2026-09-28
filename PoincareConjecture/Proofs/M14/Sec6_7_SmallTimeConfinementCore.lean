import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeConfinementEnergy
import PoincareConjecture.Proofs.M14.Mathlib.ContinuousFirstExit










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} (p : M14BackwardPath G T 0 τ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)




theorem squarePath_mapsTo_gauge_core_of_energy
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {U K : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hclock : ∀ q ∈ U, (lift q).1.val = G.spacetime.timeFunction q)
    (hKU : K ⊆ U) (hK : IsClosed K) (hxK : x ∈ interior K)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hcoercive : ∀ q ∈ K, ∀ v : EuclideanSpace ℝ (Fin n),
      κ * ‖v‖ ^ 2 ≤ ((G.gaugeCover.metric b).metric (lift q).1.val).inner (lift q).2 v v)
    (hball : MapsTo (G.gaugeCover.cylinder b).toSpacetime
      (Metric.ball (lift x) ε) (interior K))
    (hτ : τ < ε)
    (henergy : Real.sqrt τ * (∫ s in 0..Real.sqrt τ, pathSquareKinetic p s) < κ * ε ^ 2) :
    MapsTo (fun s => p.curve (s ^ 2)) (Icc 0 (Real.sqrt τ)) (interior K) := by
  by_contra hconf
  change ¬ ∀ s ∈ Icc 0 (Real.sqrt τ), p.curve (s ^ 2) ∈ interior K at hconf
  push Not at hconf
  have hcont : ContinuousOn (fun s => p.curve (s ^ 2)) (Icc 0 (Real.sqrt τ)) := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using squarePath_continuousOn p
  have hstart : p.curve (0 ^ 2) ∈ interior K := by
    simpa only [zero_pow (by decide : 2 ≠ 0), p.curve_start] using hxK
  obtain ⟨c, hc, hcexit, _, hprefix⟩ :=
    exists_first_exit_of_continuousOn hcont isOpen_interior hstart hconf
  have hsrc : ∀ s ∈ Icc 0 c, p.curve (s ^ 2) ∈ K :=
    fun s hs => closure_minimal interior_subset hK (hprefix hs)
  have hcK := hsrc c ⟨hc.1.le, le_rfl⟩
  have hxU := hKU (interior_subset hxK)
  have hcU := hKU hcK
  have hparam : c ^ 2 ∈ Icc 0 τ := squarePath_parameter_mem p (by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using ⟨hc.1.le, hc.2⟩)
  have htime : dist (lift (p.curve (c ^ 2))).1 (lift x).1 < ε := by
    rw [Subtype.dist_eq, Real.dist_eq, hclock _ hcU, hclock _ hxU,
      p.curve_time _ hparam, p.base_time, sub_zero]
    have heq : T - c ^ 2 - T = -(c ^ 2) := by ring
    rw [heq, abs_neg, abs_of_nonneg (sq_nonneg c)]
    exact hparam.2.trans_lt hτ
  have hdist : ε ≤ dist (lift (p.curve (c ^ 2))) (lift x) := by
    by_contra h
    have hm := hball (show lift (p.curve (c ^ 2)) ∈ Metric.ball (lift x) ε from
      lt_of_not_ge h)
    exact hcexit (by simpa only [hright _ hcU] using hm)
  have hspace : ε ≤ ‖(lift (p.curve (c ^ 2))).2.val - (lift x).2.val‖ := by
    rw [Prod.dist_eq] at hdist
    have hh := (le_max_iff.mp hdist).resolve_left (not_le_of_gt htime)
    simpa only [Subtype.dist_eq, dist_eq_norm] using hh
  have hlower := mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ hε.le (norm_nonneg _)).mpr hspace) hκ
  have hdisp := squarePath_gauge_prefix_displacement_le p b lift hM12 hlift hright
    hKU hκ hcoercive hc.1 (by simp) hc.2 hsrc
  have hdisp' : κ * ‖(lift (p.curve (c ^ 2))).2.val - (lift x).2.val‖ ^ 2 ≤
      Real.sqrt τ * (∫ s in 0..Real.sqrt τ, pathSquareKinetic p s) := by
    simpa only [Real.sqrt_zero, zero_pow (by decide : 2 ≠ 0), p.curve_start, sub_zero]
      using hdisp
  exact (not_lt_of_ge (hlower.trans hdisp')) henergy

end PoincareConjecture.M14
