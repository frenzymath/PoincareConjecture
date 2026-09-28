import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.FixedExtension
import Mathlib.Topology.Compactness.LocallyCompact











set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_finite_compact_tangent_cover [CompactSpace M] :
    ∃ (s : Finset M) (K : M → Set M),
      (∀ c, IsCompact (K c)) ∧
      (∀ c, K c ⊆ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) c).baseSet) ∧
      (Set.univ : Set M) = ⋃ c ∈ s, K c := by
  classical
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let e := fun c : M ↦ trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) c
  have hlocal (c : M) : ∃ K : Set M,
      IsCompact K ∧ c ∈ interior K ∧ K ⊆ (e c).baseSet :=
    exists_compact_subset (e c).open_baseSet (FiberBundle.mem_baseSet_trivializationAt' c)
  choose K hK hmem hsub using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun c ↦ interior (K c))
    (fun _ ↦ isOpen_interior)
    (show (univ : Set M) ⊆ ⋃ c, interior (K c) from
      fun c _ ↦ mem_iUnion.mpr ⟨c, hmem c⟩)
  refine ⟨s, K, hK, hsub, subset_antisymm ?_ (subset_univ _)⟩
  intro y hy
  obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp (hs hy)
  exact mem_iUnion₂.mpr ⟨c, hc, interior_subset hyc⟩

end PoincareConjecture.RicciFlowAnalysis
