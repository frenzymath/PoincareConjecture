import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.ComplementarySlabDomains
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.General.PLDomainIntersection

/-!
# Preserve regular slab geometry outside a closed replacement support

When a continuous replacement avoids the marked target frontier on
its closed support and agrees with the original map outside, every
new frontier chart is a restriction of an original chart. The exact
frontier preimage and original-atlas PL domain therefore persist.
See Waldhausen 1968, pp. 59--60.
-/

set_option autoImplicit false
open Set Geometry
open scoped Topology

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- A supported map replacement avoiding the target frontier preserves
the actual PL domain and its exact marked frontier. -/
theorem PLDomain.preimage_of_eq_off_closed
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} (q qnew : C(X, Y)) {A : Set Y}
    (he : PLDomain e (q ⁻¹' A)) (hA : IsClosed A)
    (hfront : frontier (q ⁻¹' A) = q ⁻¹' frontier A)
    {D : Set X} (hD : IsClosed D) (heq : EqOn qnew q Dᶜ)
    (havoid : Disjoint (qnew ⁻¹' frontier A) D) :
    PLDomain e (qnew ⁻¹' A) ∧ frontier (qnew ⁻¹' A) = qnew ⁻¹' frontier A := by
  have hnewfront : frontier (qnew ⁻¹' A) = qnew ⁻¹' frontier A := by
    apply Subset.antisymm (qnew.continuous.frontier_preimage_subset A)
    intro x hx
    have hxD : x ∉ D := fun h => Set.disjoint_left.mp havoid hx h
    have hxold : x ∈ frontier (q ⁻¹' A) := by
      rw [hfront]
      change q x ∈ frontier A
      rw [← heq hxD]
      exact hx
    have hxnew : x ∈ qnew ⁻¹' A :=
      hA.frontier_subset hx
    apply (mem_frontier_iff_notMem_interior hxnew).mpr
    intro hi
    have hlocal : (qnew ⁻¹' A) =ᶠ[𝓝 x] (q ⁻¹' A) := by
      filter_upwards [hD.isOpen_compl.mem_nhds hxD] with y hy
      change (qnew y ∈ A) = (q y ∈ A)
      rw [heq hy]
    exact Set.disjoint_left.mp disjoint_interior_frontier (hlocal.mem_interior hi) hxold
  refine ⟨⟨he.cover, he.compatible, hA.preimage qnew.continuous, ?_⟩, hnewfront⟩
  intro x hx
  have hxmark := hnewfront.subset hx
  have hxD : x ∉ D := fun h => Set.disjoint_left.mp havoid hxmark h
  have hxold : x ∈ frontier (q ⁻¹' A) := by
    rw [hfront]
    change q x ∈ frontier A
    rw [← heq hxD]
    exact hxmark
  obtain ⟨ell, v, B, hv, hxB, hzero, hPL, hhalf⟩ := he.halfspace x hxold
  let C := B.restrOpen Dᶜ hD.isOpen_compl
  refine ⟨ell, v, C, hv, ⟨hxB, hxD⟩, hzero, ?_, ?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right B (hPL i) hD.isOpen_compl
  · intro y hy
    change qnew y ∈ A ↔ 0 ≤ ell (B y)
    rw [heq hy.2]
    exact hhalf y hy.1

end PoincareMT.M76
