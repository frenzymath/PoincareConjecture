import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.ChartedSpace
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Geometry.Manifold.RegularLevel

theorem finite_connectedComponents_of_compact_regular_level
    {n : Nat} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {f : M -> Real} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(Real, Real) ∞ f)
    (c : Real) (hc : IsCompact (f ⁻¹' {c}))
    (hreg : ∀ x, f x = c -> mfderiv (𝓡 (n + 1)) 𝓘(Real, Real) f x ≠ 0) :
    Finite (ConnectedComponents (f ⁻¹' {c} : Set M)) := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin (n + 1))) = n + 1) :=
    ⟨by simp⟩
  let := levelSetChartedSpace hf n c hreg
  let : CompactSpace (f ⁻¹' {c} : Set M) := isCompact_iff_compactSpace.mp hc
  let : LocallyConnectedSpace (f ⁻¹' {c} : Set M) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace Real (Fin n)) _
  infer_instance

end Poincare.Geometry.Manifold.RegularLevel
