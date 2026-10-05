import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionPLLocalInterior
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionIncidence

/-!
# Actual ambient regions of equal-dimensional finite PL balls

Finite PL openness in both chart directions identifies the
ambient interior with the complement of the specified boundary.
This supplies the actual open connected region, dense closure
and frontier used in bounded-region incidence.
See Alexander 1924, p. 7, Hudson 1969, pp. 60--61 and
M76 derivation 247.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- A finite PL ball in its model dimension has precisely
its prescribed boundary complement as ambient interior.
The equality includes the zero-dimensional case.
See Hudson pp. 60--61 and M76 derivation 247. -/
theorem IsFinitePLBallPair.interior_eq_sdiff_of_finrank_eq
    {s b : Set X} (hs : IsFinitePLBallPair E s b)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ X) : interior s = s \ b := by
  apply Subset.antisymm _ (hs.sdiff_subset_interior_of_finrank_eq hdim)
  obtain ⟨_, C, _, _, _, e, he, heb⟩ := hs
  obtain ⟨f, hf, hfv⟩ := he
  have hinj : InjOn f s := by
    intro x hx y hy hxy
    have h : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
      Subtype.ext ((hfv ⟨x, hx⟩).trans (hxy.trans (hfv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (e.injective h)
  have hmap : f '' s ⊆ C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hfv ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  intro x hx
  refine ⟨interior_subset hx, ?_⟩
  intro hxb
  have hfx : f x ∈ interior C :=
    interior_mono hmap (hf.mem_interior_image hdim.symm hinj hx)
  have hboundary := (heb ⟨x, interior_subset hx⟩).mp hxb
  rw [hfv] at hboundary
  exact hboundary.2 hfx

/-- The actual ambient frontier of a finite PL ball in its
model dimension is its specified boundary.
See Alexander p. 7 and M76 derivation 247. -/
theorem IsFinitePLBallPair.frontier_eq_of_finrank_eq
    {s b : Set X} (hs : IsFinitePLBallPair E s b)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ X) : frontier s = b := by
  rw [frontier, hs.isCompact.isClosed.closure_eq, hs.interior_eq_sdiff_of_finrank_eq hdim]
  ext x
  change (x ∈ s ∧ ¬ (x ∈ s ∧ x ∉ b)) ↔ x ∈ b
  constructor
  · intro hx
    by_contra hxb
    exact hx.2 ⟨hx.1, hxb⟩
  · intro hx
    exact ⟨hs.1 hx, fun h => h.2 hx⟩

/-- The ambient interior of a finite PL ball in its model
dimension is dense in the whole ball carrier.
See Alexander p. 7 and M76 derivation 247. -/
theorem IsFinitePLBallPair.closure_interior_of_finrank_eq
    {s b : Set X} (hs : IsFinitePLBallPair E s b)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ X) : closure (interior s) = s := by
  rw [hs.interior_eq_sdiff_of_finrank_eq hdim]
  exact hs.closure_sdiff

/-- The ambient interior of a finite PL ball in its model
dimension is connected and nonempty.
See Alexander p. 7 and M76 derivation 247. -/
theorem IsFinitePLBallPair.isConnected_interior_of_finrank_eq
    {s b : Set X} (hs : IsFinitePLBallPair E s b)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ X) : IsConnected (interior s) := by
  rw [hs.interior_eq_sdiff_of_finrank_eq hdim]
  exact hs.isConnected_sdiff

/-- The ambient open region inside a finite PL ball has
exactly the specified boundary as its frontier.
See Alexander p. 7 and M76 derivation 247. -/
theorem IsFinitePLBallPair.frontier_interior_of_finrank_eq
    {s b : Set X} (hs : IsFinitePLBallPair E s b)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ X) :
    frontier (interior s) = b := by
  rw [frontier, hs.closure_interior_of_finrank_eq hdim, interior_interior]
  have hfront := hs.frontier_eq_of_finrank_eq hdim
  rwa [frontier, hs.isCompact.isClosed.closure_eq] at hfront

end Set
