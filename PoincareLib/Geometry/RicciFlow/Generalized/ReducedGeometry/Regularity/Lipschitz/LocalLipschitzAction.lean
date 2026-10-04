import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.PathCongruence
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential

/-!
# Comparing actual minimizing actions with a local survivor branch

The local inverse branch is an admissible competitor even before its
minimality is known. Its actual clock identifies the endpoint time.
All comparisons use genuine path actions, not a totalized infimum.
Morgan-Tian Proposition 6.59, pp. 134-137.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T b : ℝ} {x y : G.Point}

/-- A minimizing actual action is bounded by any surviving exponential
competitor with the same actual endpoint, Proposition 6.59, pp. 134-137. -/
theorem minimizing_action_le_exponentialAction (E : M14ExponentialFamily G T x)
    (p : M14BackwardPath G T 0 b x y) (hp : M14IsMinimizing p)
    {Z : G.Horizontal x} {s : ℝ} (hD : (Z, s) ∈ E.domain) (hs : 0 < s)
    (hpoint : E.gamma Z s = y) : M14BackwardLAction G p ≤ E.action Z s := by
  subst y
  have hb : b = s ^ 2 := by linarith [p.endpoint_time, E.clock Z s hD]
  subst b
  rw [E.action_eq Z s hD hs]
  exact hp (E.path Z s hD hs)

/-- Agreement of actual backward curves with a surviving branch
identifies their actions, including their exact endpoint times,
equation (6.2) and Proposition 6.59, pp. 106, 134-137. -/
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

/-- A minimizing supplied branch identifies the raw spacetime reduced
length with its normalized action, Definition 6.45, p. 129. -/
theorem reducedLengthAt_exponential_of_minimizing (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hD : (Z, s) ∈ E.domain) (hs : 0 < s)
    (hp : M14IsMinimizing (E.path Z s hD hs)) :
    M14ReducedLengthAt G T 0 x (E.gamma Z s) = E.action Z s / (2 * s) := by
  unfold M14ReducedLengthAt
  rw [E.clock Z s hD, sub_sub_cancel, ← E.reduced_length_global_eq Z s hD hs hp,
    E.reduced_length_eq Z s hD hs]

end PoincareMT.M14
