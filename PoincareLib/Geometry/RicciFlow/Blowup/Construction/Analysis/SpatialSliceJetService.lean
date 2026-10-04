import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Explicit supplier for spatial slices of within-jet convergence

This is the exact proposition of the unpublished M28 theorem
`TendstoUniformlyOn.iteratedFDeriv_spatial_slice`. It retains the source
filter, full derivative domain, smoothness and tested set. No inhabitant
or new analytic slicing theorem is supplied.

Reference: Morgan--Tian Proposition 5.14, pp. 90--91, and
Proposition 9.79(4), pp. 233--234. The donor pin and publication obligation
are recorded in
`proof-work/tasks/M30/derivations/spatial-slice-jet-service.md`.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

universe uField uTime uSpace uValue uIndex

namespace PoincareMT.M30

/-- The unfilled lower supplier taking uniform within-jet convergence on
a time-space product to uniform ordinary spatial-jet convergence on the
same tested set, including included time endpoints
(Morgan--Tian Proposition 5.14, pp. 90--91;
Proposition 9.79(4), pp. 233--234). -/
def SpatialSliceJetConvergenceService : Prop :=
  ∀ {𝕜 : Type uField} {T : Type uTime} {E : Type uSpace} {F : Type uValue}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {α : Type uIndex} {l : Filter α}
    {J : Set T} {U : Set E} {K : Set (T × E)}
    {f : α → T × E → F} {g : T × E → F} {n : ℕ∞ω} {r : ℕ},
    TendstoUniformlyOn
      (fun k => iteratedFDerivWithin 𝕜 r (f k) (J ×ˢ U))
      (iteratedFDerivWithin 𝕜 r g (J ×ˢ U)) l K →
    UniqueDiffOn 𝕜 J → IsOpen U → K ⊆ J ×ˢ U →
    (∀ᶠ k in l, ContDiffOn 𝕜 n (f k) (J ×ˢ U)) →
    ContDiffOn 𝕜 n g (J ×ˢ U) → r ≤ n →
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv 𝕜 r (fun y => f k (p.1, y)) p.2)
      (fun p => iteratedFDeriv 𝕜 r (fun y => g (p.1, y)) p.2) l K

end PoincareMT.M30
