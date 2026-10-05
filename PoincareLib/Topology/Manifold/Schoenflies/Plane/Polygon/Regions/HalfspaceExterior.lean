import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Order.Bornology
import Mathlib.Tactic.Linarith

/-!
# Strict supporting half-spaces belong to unbounded components

The exterior-side ingredient for the supporting-vertex proof in Munkres
(1960), Lemma 2.3, p. 195. A surjective continuous real linear functional
makes every strict sublevel half-space unbounded. Convexity absorbs that
half-space into a single component of a disjoint set's complement.
See `smale/derivations/2026-09-21-region-linear-bounds.md` for the derivation.
-/

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A strict half-space of a surjective real linear functional is unbounded;
the supporting-line exterior ingredient for Munkres, Lemma 2.3, p. 195. -/
theorem not_isBounded_lt_halfspace (X : E →L[ℝ] ℝ) (hX : Function.Surjective X)
    (c : ℝ) : ¬ Bornology.IsBounded {x | X x < c} := by
  intro h
  obtain ⟨b, hb⟩ := (X.lipschitz.isBounded_image h).bddBelow
  obtain ⟨z, hz⟩ := hX (min b c - 1)
  have hzH : X z < c := by
    rw [hz]
    have := min_le_right b c
    linarith
  have hbz : b ≤ X z := hb ⟨z, hzH, rfl⟩
  rw [hz] at hbz
  have := min_le_left b c
  linarith

/-- Points strictly below a set's linear lower bound have unbounded complement
components; the exterior-side argument for Munkres, Lemma 2.3, p. 195. -/
theorem not_isBounded_compl_component_of_lt_linear_bound (X : E →L[ℝ] ℝ)
    (hX : Function.Surjective X) (c : ℝ) {C : Set E}
    (hC : C ⊆ {z | c ≤ X z}) {x : E} (hx : X x < c) :
    ¬ Bornology.IsBounded (connectedComponentIn Cᶜ x) := by
  have hconn : IsPreconnected {z | X z < c} :=
    ((convex_Iio (𝕜 := ℝ) c).linear_preimage X.toLinearMap).isPreconnected
  have hsub : {z | X z < c} ⊆ Cᶜ := by
    intro z hz hzC
    exact (not_lt_of_ge (show c ≤ X z from hC hzC)) hz
  have hcomp : {z | X z < c} ⊆ connectedComponentIn Cᶜ x :=
    hconn.subset_connectedComponentIn hx hsub
  exact fun hb => not_isBounded_lt_halfspace X hX c (hb.subset hcomp)

end Poincare.Manifold.Schoenflies.Plane
