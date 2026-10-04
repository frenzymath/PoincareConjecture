import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialVector

/-!
# Injectivity on a fixed stable carrier

Morgan-Tian Definitions 6.25-6.27 and Proposition 6.28, pp. 116-117.
Uniqueness of the minimizing path gives branch equality; the actual initial
derivative then recovers the initial vector. No endpoint injectivity is assumed.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point}

private theorem minimizing_curves_eqOn_of_endpoint_eq {y z : G.Point}
    (p : M14BackwardPath G T 0 τ x y) (q : M14BackwardPath G T 0 τ x z)
    (h : y = z)
    (hunique : ∀ r : M14BackwardPath G T 0 τ x y,
      M14IsMinimizing r → Set.EqOn r.curve p.curve (Set.Icc 0 τ))
    (hq : M14IsMinimizing q) : Set.EqOn q.curve p.curve (Set.Icc 0 τ) := by
  cases h
  exact hunique q hq

/-- The actual spacetime endpoint is injective on the stable carrier,
Morgan-Tian Proposition 6.28, p. 117. -/
theorem stable_endpoint_injective {E : M14ExponentialFamily G T x}
    (H : M14StableSet G T τ x E) : Set.InjOn H.endpoint_map H.carrier := by
  intro Z hZ W hW heq
  obtain ⟨p, hpcurve, _, hpunique⟩ := H.minimizing_path Z hZ
  obtain ⟨q, hqcurve, hqmin, _⟩ := H.minimizing_path W hW
  have hqp := minimizing_curves_eqOn_of_endpoint_eq p q heq hpunique hqmin
  have hbranch : Set.EqOn (fun t => E.gamma Z (Real.sqrt t))
      (fun t => E.gamma W (Real.sqrt t)) (Set.Icc 0 τ) := by
    intro t ht
    exact (hpcurve ht).symm.trans ((hqp ht).symm.trans (hqcurve ht))
  apply initialVector_eq_of_backward_branches_eqOn E
    (H.survivor Z hZ) (H.survivor W hW) (Real.sqrt_pos.mpr H.tau_pos)
  simpa only [Real.sq_sqrt H.tau_pos.le] using hbranch

/-- The endpoint in the actual earlier-time slice is injective on the same
stable carrier, Morgan-Tian Proposition 6.28, p. 117. -/
theorem stable_slice_endpoint_injective {E : M14ExponentialFamily G T x}
    (H : M14StableSet G T τ x E) : Set.InjOn H.endpoint_slice_map H.carrier := by
  intro Z hZ W hW heq
  apply stable_endpoint_injective H hZ hW
  calc
    H.endpoint_map Z = (H.endpoint_slice_map Z).val :=
      (H.endpoint_slice_map_val Z hZ).symm
    _ = (H.endpoint_slice_map W).val := congrArg Subtype.val heq
    _ = H.endpoint_map W := H.endpoint_slice_map_val W hW

end PoincareMT.M14
