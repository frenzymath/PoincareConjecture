import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SmallTime.Candidates.SmallTimeCandidateSmooth

/-!
# Actual coordinate speeds of restricted exponential candidates

The supplied path agrees with the smooth family on each closed short
square interval. Unique within derivatives at both endpoints preserve
the uniform coordinate-speed bound under restriction.
Morgan-Tian Lemma 6.22 and Corollary 6.79, pp. 115-116, 144-145.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- Restricting the common coordinate derivative bound gives the
actual supplied path's speed bound through both closed short-time
endpoints, Lemma 6.22 and Corollary 6.79, pp. 115-116, 144-145. -/
theorem smallTimeCandidate_coordinate_speed_le (E : M14ExponentialFamily G T x)
    (b : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    (W : G.Horizontal x) {s d M : ℝ} (hs : 0 < s) (hsd : s ≤ d)
    (hD : (W, s) ∈ E.domain)
    (hcoord : ContDiffOn ℝ ∞ (fun r => (lift (E.gamma W r)).2.val) (Icc 0 d))
    (hM : ∀ r ∈ Icc 0 d,
      ‖derivWithin (fun t => (lift (E.gamma W t)).2.val) (Icc 0 d) r‖ ≤ M) :
    ∀ r ∈ Icc 0 s,
      ‖derivWithin (fun t => (lift ((E.path W s hD hs).curve (t ^ 2))).2.val)
        (Icc 0 s) r‖ ≤ M := by
  have hsub : Icc 0 s ⊆ Icc 0 d := fun _ hr => ⟨hr.1, hr.2.trans hsd⟩
  have heq : EqOn (fun t => (lift ((E.path W s hD hs).curve (t ^ 2))).2.val)
      (fun t => (lift (E.gamma W t)).2.val) (Icc 0 s) := by
    intro t ht
    have hsq : t ^ 2 ∈ Icc 0 (s ^ 2) :=
      ⟨sq_nonneg t, (sq_le_sq₀ ht.1 hs.le).mpr ht.2⟩
    change (lift ((E.path W s hD hs).curve (t ^ 2))).2.val = (lift (E.gamma W t)).2.val
    rw [E.path_coherent W s hD hs (t ^ 2) hsq, Real.sqrt_sq ht.1]
  intro r hr
  rw [derivWithin_congr heq (heq hr), derivWithin_subset hsub
    (uniqueDiffOn_Icc hs r hr) ((hcoord r (hsub hr)).differentiableWithinAt (by simp))]
  exact hM r (hsub hr)

end PoincareMT.M14
