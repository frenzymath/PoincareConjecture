import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedronNeighborhoodRetraction
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FinitePiecewiseAffine
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.LocallyFinitePolyhedralPatches

/-!

# Extending finite PL maps to actual open neighborhoods

Compose a finite PL map with an actual finite polyhedral
neighborhood retraction. The result agrees on the entire
original carrier and is locally PL on an ambient open
neighborhood. See Hudson 1969, pp. 15--19, Hatcher,
Theorem 3.1, p. 45 and M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every finite PL map extends, with exactly its original
values, to a locally PL map on an actual ambient open
neighborhood of its complete carrier. The original carrier
may have empty ambient interior. See Hudson pp. 15--19 and
M76 derivation 270. -/
theorem FinitePiecewiseAffineOn.exists_locallyPiecewiseAffine_extension
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S) :
    ∃ (g : E → F) (U : Set E), IsOpen U ∧ S ⊆ U ∧
      LocallyPiecewiseAffineOn g U ∧ EqOn g f S := by
  classical
  obtain ⟨K, hK, rfl, hfK⟩ := hf
  obtain ⟨N, r, hN, hKN, _, hr, hrK, hrfix⟩ :=
    K.exists_finitePL_neighborhood_retraction hK isOpen_univ (subset_univ _)
  let g := f ∘ r
  have hg : FinitePiecewiseAffineOn g N.space :=
    (hfK.finitePiecewiseAffineOn hK).comp (hr.finitePiecewiseAffineOn hN) hrK
  obtain ⟨R, hR, hRN, hgR⟩ := hg
  let : Fintype R.faces := hR.fintype
  have hlocal : LocallyPiecewiseAffineOn g (interior R.space) :=
    hgR.locallyPiecewiseAffineOn_of_locallyFinite
      (locallyFinite_of_finite (fun s : R.faces => convexHull ℝ (s.val : Set E)))
  refine ⟨g, interior R.space, isOpen_interior, ?_, hlocal, ?_⟩
  · rwa [hRN]
  · intro x hx
    change f (r x) = f x
    rw [hrfix hx]
    rfl

end Geometry
