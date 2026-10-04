import PoincareLib.Topology.Manifold.Poincare.Final.Main

/-!
# Smooth and topological Poincare theorems

Imported from `PoincareMT/Proofs/Main.lean` at
`a27691488baa6c690f50afc23376abb51abd2f9c`, preserving both endpoint statements
and proof terms. The smooth branch applies M75 directly; the topological
branch projects the final package. Neither endpoint has a predecessor-package
argument. Recursive dependency verification is performed by
`scripts/check_poincare_endpoints.lean`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Every compact Hausdorff second-countable simply connected smooth
three-manifold is diffeomorphic to the standard three-sphere. Source:
Morgan--Tian Corollary 0.2(a), assembled through the numbered skeleton. -/
theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  exact m75SmoothPoincare m90SmoothEndpointInputs

/-- Every compact Hausdorff second-countable simply connected topological
three-manifold is homeomorphic to the standard three-sphere. Apply smooth
Poincare through M76's compatible smoothing and the checked M77--M90 route;
no smoothness hypothesis is imposed on the original manifold. -/
theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  obtain ⟨C⟩ := m90FinalAssemblyFromMilestones.{u}
  exact C.topological

end PoincareMT
