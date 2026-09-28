import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Order.Bornology
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

end PoincareConjecture.M25.Topology3D
