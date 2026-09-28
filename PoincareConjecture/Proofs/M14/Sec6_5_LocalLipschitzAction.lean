import PoincareConjecture.Proofs.M14.Sec6_1_PathCongruence
import PoincareConjecture.Definitions.M14Exponential

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T b : ℝ} {x y : G.Point}

theorem minimizing_action_le_exponentialAction (E : M14ExponentialFamily G T x)
    (p : M14BackwardPath G T 0 b x y) (hp : M14IsMinimizing p)
    {Z : G.Horizontal x} {s : ℝ} (hD : (Z, s) ∈ E.domain) (hs : 0 < s)
    (hpoint : E.gamma Z s = y) : M14BackwardLAction G p ≤ E.action Z s := by
  subst y
  have hb : b = s ^ 2 := by linarith [p.endpoint_time, E.clock Z s hD]
  subst b
  rw [E.action_eq Z s hD hs]
  exact hp (E.path Z s hD hs)

theorem action_eq_exponentialAction_of_curve_eqOn (E : M14ExponentialFamily G T x)
    (p : M14BackwardPath G T 0 b x y)
    {Z : G.Horizontal x} {s : ℝ} (hD : (Z, s) ∈ E.domain) (hs : 0 < s)
    (hpoint : E.gamma Z s = y)
    (hcurve : EqOn p.curve (fun t => E.gamma Z (Real.sqrt t)) (Icc 0 b)) :
    M14BackwardLAction G p = E.action Z s := by
  subst y
  have hb : b = s ^ 2 := by linarith [p.endpoint_time, E.clock Z s hD]
  subst b
  rw [E.action_eq Z s hD hs]
  apply action_eq_of_curve_eqOn p (E.path Z s hD hs)
  intro t ht
  exact (hcurve (Ioo_subset_Icc_self ht)).trans (E.path_coherent Z s hD hs t
    (Ioo_subset_Icc_self ht)).symm

theorem reducedLengthAt_exponential_of_minimizing (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hD : (Z, s) ∈ E.domain) (hs : 0 < s)
    (hp : M14IsMinimizing (E.path Z s hD hs)) :
    M14ReducedLengthAt G T 0 x (E.gamma Z s) = E.action Z s / (2 * s) := by
  unfold M14ReducedLengthAt
  rw [E.clock Z s hD, sub_sub_cancel, ← E.reduced_length_global_eq Z s hD hs hp,
    E.reduced_length_eq Z s hD hs]

end PoincareConjecture.M14
