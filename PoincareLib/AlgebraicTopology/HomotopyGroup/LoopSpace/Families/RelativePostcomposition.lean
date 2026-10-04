import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.Postcomposition

/-!
# Naturality for the relative loop square

The three fixed edges and the constant fourth edge are preserved by the actual
loop map, at every time of a homotopy. Source: Perelman III, Section 1, p. 1;
MT Claim 18.16, printed p. 430.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareMT

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]

/-- Actual postcomposition preserves the relative square boundary condition.
Source: Perelman III, Section 1, p. 1. -/
theorem m59RelativeLoopCubeAt_postcompose {f : C(M, N)} (L : M59LoopPostcomposition f)
    {x : M} {F : C((Fin 2 → I), C1FreeLoopSpace (M := M))}
    (hF : M59RelativeLoopCubeAt x F) :
    M59RelativeLoopCubeAt (f x) (L.map.comp F) := by
  constructor
  · intro z hz
    change L.map (F z) = _
    rw [hF.1 z hz, L.maps_constant]
  · intro z hz
    obtain ⟨p, hp⟩ := hF.2 z hz
    refine ⟨f p, ?_⟩
    change L.map (F z) = _
    rw [hp, L.maps_constant]

/-- A homotopy through relative loop squares postcomposes through the same
relative boundary condition. Source: Perelman III, Section 1, p. 1. -/
theorem m59_relative_naturality (f : C(M, N)) (L : M59LoopPostcomposition f)
    (x : M) (F G : C((Fin 2 → I), C1FreeLoopSpace (M := M)))
    (H : ContinuousMap.HomotopicWith F G (M59RelativeLoopCubeAt x)) :
    ContinuousMap.HomotopicWith (L.map.comp F) (L.map.comp G)
      (M59RelativeLoopCubeAt (f x)) := by
  obtain ⟨H⟩ := H
  refine ⟨{
    toHomotopy := (ContinuousMap.Homotopy.refl L.map).comp H.toHomotopy
    prop' := fun t => ?_ }⟩
  exact m59RelativeLoopCubeAt_postcompose L (H.prop t)

end PoincareMT
