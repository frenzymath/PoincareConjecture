import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Domain.JointNeighborhood
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StableOpenness
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.PathCongruence
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.LLength

/-!
# Actual minimizing branches on the joint domain

The stable graph supplies a stable set at exactly the squared joint
time. Its minimizing branch agrees with the selected exponential
path, so the selected action and reduced length are the actual
infima. Morgan-Tian Proposition 6.28, p. 117, and Definition 6.45,
p. 129.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- Every joint-domain point belongs to a stable carrier at its exact
squared time, Proposition 6.28, p. 117. -/
theorem jointDomain_stableSet (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hz : (Z, s) ∈ M14JointDomain G E) :
    ∃ H : M14StableSet G T (s ^ 2) x E, Z ∈ H.carrier := by
  obtain ⟨τ, H, hτ, hZ, hs⟩ := hz.1
  change s = Real.sqrt τ at hs
  have heq : τ = s ^ 2 := by rw [hs, Real.sq_sqrt hτ.le]
  subst τ
  exact ⟨H, hZ⟩

/-- The actual selected branch on the joint domain minimizes, and its
action and reduced length are the global values at that endpoint,
Proposition 6.28, p. 117, and Definition 6.45, p. 129. -/
theorem jointDomain_action_branch (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hz : (Z, s) ∈ M14JointDomain G E) :
    ∃ H : M14StableSet G T (s ^ 2) x E, Z ∈ H.carrier ∧
      ∃ p : M14BackwardPath G T 0 (s ^ 2) x (E.gamma Z s),
        M14IsMinimizing p ∧ E.action Z s = M14BackwardLAction G p ∧
        E.reduced_length Z s = M14ReducedLengthValue G T 0 (s ^ 2) x (E.gamma Z s) := by
  have hpos : 0 < s := jointDomain_time_pos E hz
  have hsurv := jointDomain_subset_domain E hz
  obtain ⟨H, hZH⟩ := jointDomain_stableSet E hz
  have hb := stableInitialVector_unique_branch E ((H.carrier_exact Z).mp hZH)
  unfold M14UniqueMinimizingBranch at hb
  rw [Real.sqrt_sq hpos.le] at hb
  obtain ⟨_, p, hpcurve, hpmin, _⟩ := hb
  let R := E.path Z s hsurv hpos
  have hcurve : EqOn R.curve p.curve (Ioo 0 (s ^ 2)) := by
    intro r hr
    exact (E.path_coherent Z s hsurv hpos r (Ioo_subset_Icc_self hr)).trans
      (hpcurve (Ioo_subset_Icc_self hr)).symm
  have hmin : M14IsMinimizing R := (isMinimizing_iff_of_curve_eqOn R p hcurve).mpr hpmin
  refine ⟨H, hZH, R, hmin, E.action_eq Z s hsurv hpos, ?_⟩
  calc
    E.reduced_length Z s = E.action Z s / (2 * s) := E.reduced_length_eq Z s hsurv hpos
    _ = M14BackwardLAction G R / (2 * Real.sqrt (s ^ 2)) := by
      rw [Real.sqrt_sq hpos.le, E.action_eq Z s hsurv hpos]
    _ = M14ReducedLengthValue G T 0 (s ^ 2) x (E.gamma Z s) :=
      (reducedLengthValue_eq_of_minimizing R hmin).symm

end PoincareMT.M14
