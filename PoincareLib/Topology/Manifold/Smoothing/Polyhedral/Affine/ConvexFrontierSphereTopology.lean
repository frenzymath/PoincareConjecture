import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexFrontierOtherPoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectedness and nontriviality of actual convex-frontier spheres

The checked unit-sphere homeomorphism transfers Mathlib's
connectedness theorem. An actual different frontier point
supplies nontriviality of the unchanged source carrier.
See Cairns 1940, pp. 801--802 and M76 derivation 281.
-/

set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A space homeomorphic to a compact convex frontier in
real dimension greater than one is connected. Only the
topology is transported. See M76 derivation 281. -/
theorem isConnected_of_convex_frontier
    {s : Set X} {C : Set E} (e : s ≃ₜ frontier C)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : 1 < Module.finrank ℝ E) : IsConnected s := by
  obtain ⟨_, f, _⟩ := hC.exists_compatible_unitBall_models hcv hne
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdim
  have hunit : IsConnected (sphere (0 : E) 1) :=
    isConnected_sphere hrank 0 zero_le_one
  exact isConnected_iff_connectedSpace.mpr
    ((e.trans f).connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp hunit))

/-- The same actual convex-frontier sphere carrier contains
two different points, chosen through its actual frontier
model. See Cairns pp. 801--802 and M76 derivation 281. -/
theorem nontrivial_of_convex_frontier
    {s : Set X} {C : Set E} (e : s ≃ₜ frontier C)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : 1 < Module.finrank ℝ E) : s.Nontrivial := by
  obtain ⟨x, hx⟩ := (e.isConnected_of_convex_frontier hC hcv hne hdim).nonempty
  obtain ⟨y, hy⟩ := hC.exists_ne_frontier_point hcv hne (e ⟨x, hx⟩)
  refine ⟨x, hx, e.symm y, (e.symm y).property, ?_⟩
  intro h
  apply hy
  have heq : e.symm y = ⟨x, hx⟩ := Subtype.ext h.symm
  simpa only [e.apply_symm_apply] using congrArg e heq

end Homeomorph
