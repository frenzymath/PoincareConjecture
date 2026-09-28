import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

universe uField uTime uSpace uValue uIndex

namespace PoincareConjecture.M30

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

end PoincareConjecture.M30
