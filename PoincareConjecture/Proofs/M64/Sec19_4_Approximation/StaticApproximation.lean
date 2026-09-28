import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformCompactApproximation
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformRawFamily
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.StaticTheoryAssembly

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m64StaticApproximationTheory_of_compact
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M)) :
    M64StaticApproximationTheory g D :=
  m64StaticApproximationTheory_of_suppliers hcompact
    (fun X hX _zeta hzeta => m64_uniform_compact_approximation g D hcompact X hX hzeta)
    (fun Gamma hnull _zeta hzeta => m64_uniform_raw_family g D hcompact Gamma hnull hzeta)

end PoincareConjecture
