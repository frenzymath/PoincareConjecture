import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierOtherPoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

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
