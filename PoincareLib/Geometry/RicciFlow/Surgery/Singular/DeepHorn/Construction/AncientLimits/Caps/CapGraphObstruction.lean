import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Compactness.CompactPartialInverse
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Topology.ProductGraphBoundary
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Cap
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareLib.Topology.Manifold.NeckCap.Theory

/-!
# An actual cap cannot have a graph boundary in a partial product image

Morgan--Tian Claim 11.35, printed p. 290. The entire compact core and its
ambient frontier are first transported through the guarded partial
inverse. Only then is the global product chart on the limit applied.
The core inclusion rederives the elementary
`CapCertificate.closed_core_subset_carrier` from read-only M34
`Thm12_28_12_29_Lifetime/CapPersistenceNormalization.lean`.
Reviewed derivation: `claim11_35-fixed-time-cap-exclusion.md`, section 6.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v w

namespace PoincareMT.M32

/-- Either cap model contradicts a graph boundary after its complete core
is transported into the actual global product (Claim 11.35, p. 290). -/
theorem cap_not_in_partial_product_with_graph_boundary
    {M : Type u} {L : Type v} {X : Type w}
    [TopologicalSpace M] [TopologicalSpace L] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [T2Space L]
    {gM : RiemannianMetric 3 M} (C : CapCertificate gM)
    (E : OpenPartialHomeomorph L M) (hC : C.carrier ⊆ E.target)
    (Phi : (X × ℝ) ≃ₜ L) (H : X → ℝ) (hH : Continuous H)
    (hboundary : ∀ y ∈ C.boundary_sphere,
      (Phi.symm (E.symm y)).2 = H ((Phi.symm (E.symm y)).1)) : False := by
  have hcore : C.closed_core ⊆ E.target := by
    intro y hy
    rw [C.closed_core_eq_complement_end] at hy
    exact hC hy.1
  obtain ⟨hcompact, _, hint, hfront⟩ :=
    compact_partial_inverse_geometry E C.closed_core_compact hcore
  have hnonempty : (interior (E.symm '' C.closed_core)).Nonempty := by
    rw [hint, ← C.core_eq_interior_closed_core]
    exact C.core_nonempty.image E.symm
  let e : (univ : Set L) ≃ₜ X × ℝ := (Homeomorph.Set.univ L).trans Phi.symm
  apply not_isCompact_of_product_graph_frontier isOpen_univ (subset_univ _)
    e H hH hnonempty ?_ hcompact
  rintro z ⟨y, hy, rfl⟩
  change (Phi.symm y.val).2 = H ((Phi.symm y.val).1)
  change y.val ∈ frontier (E.symm '' C.closed_core) at hy
  rw [hfront, C.core_frontier_eq_boundary] at hy
  obtain ⟨a, ha, hea⟩ := hy
  rw [← hea]
  exact hboundary a ha

end PoincareMT.M32
