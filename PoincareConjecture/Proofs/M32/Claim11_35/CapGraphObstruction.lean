import PoincareConjecture.Proofs.M32.Mathlib.CompactPartialInverse
import PoincareConjecture.Proofs.M32.Mathlib.ProductGraphBoundary
import PoincareConjecture.Definitions.Ch09.NeckCapTopology

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v w

namespace PoincareConjecture.M32

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

end PoincareConjecture.M32
