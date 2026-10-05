import PoincareLib.Topology.Manifold.Smoothing.CompactCore.General.ProtectedPLIntersection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Topology.CompactPLHalfspaceNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.AtlasOfCover

/-!
# A protected PL core using the literal weak end condition

The compact ambient neighborhood protects the supplied compact set,
the whole old boundary and the deeper compact set chosen by the
unchanged end predicate. Its intersection with the original domain
has the exact ambient and relative frontiers, and all new-frontier
loops have actual contractions avoiding the earlier protected set.
See Hamilton 1976, Lemma 2, pp. 64--65, and M76 Wall derivation 002.
This is the preliminary core for compression, not Wall's new sphere.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The frozen end hypothesis constructs a compact original PL core
retaining the whole old boundary, with exact relative frontier and
actual contractions of all its new-frontier loops. The deeper compact
complement remains connected; it is not assumed simply connected.
No connectedness or sphere type of the new frontier is asserted.
See Hamilton Lemma 2 and Wall derivation 002. -/
theorem exists_weak_end_protected_PL_core
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X}
    (hR : PLDomain e R) (hB : IsCompact (frontier R))
    (hend : HasOneSimplyConnectedEnd R)
    {A : Set X} (hA : IsCompact A) (hAR : A ⊆ R)
    {C : Set R} (hC : IsCompact C) :
    ∃ D : Set R, IsCompact D ∧ C ⊆ interior D ∧ IsConnected Dᶜ ∧
      ∃ K S : Set X, IsCompact K ∧ A ⊆ K ∧ K ⊆ R ∧ PLDomain e K ∧
        IsCompact S ∧ S ⊆ interior R ∧ Disjoint (frontier R) S ∧
        frontier K = frontier R ∪ S ∧
        (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
          interior ((Subtype.val : R → X) ⁻¹' K) ∧
        frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' S ∧
        Disjoint ((Subtype.val : R → X) '' D) S ∧
        ∀ (x : R) (p : Path x x),
          (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' S) →
          ∃ H : p.Homotopy (Path.refl x), ∀ z, H z ∉ C := by
  obtain ⟨D, hD, hCD, hconn, hloops⟩ := hend C hC
  let := ChartedSpace.ofChartCover e hR.cover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  let Z : Set X := (A ∪ frontier R) ∪ (Subtype.val : R → X) '' D
  have hZ : IsCompact Z := (hA.union hB).union (hD.image continuous_subtype_val)
  obtain ⟨P, hP, hZP, _, hhalf⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e hR.compatible
      hR.cover hZ isOpen_univ (subset_univ _)
  have hPi : PLDomain e P := ⟨hR.cover, hR.compatible, hP.isClosed, hhalf⟩
  have hBP : frontier R ⊆ interior P := fun _ hx => hZP (Or.inl (Or.inr hx))
  let K : Set X := P ∩ R
  let S : Set X := frontier P ∩ R
  have hS : IsCompact S :=
    (hP.of_isClosed_subset isClosed_frontier hP.isClosed.frontier_subset).inter_right hR.closed
  have hDS : Disjoint ((Subtype.val : R → X) '' D) S := by
    apply disjoint_left.mpr
    intro x hxD hxS
    exact hxS.1.2 (hZP (Or.inr hxD))
  have hpreK : (Subtype.val : R → X) ⁻¹' K = (Subtype.val : R → X) ⁻¹' P := by
    ext x
    exact and_iff_left x.property
  refine ⟨D, hD, hCD, hconn, K, S, hP.inter_right hR.closed, ?_,
    inter_subset_right, hPi.inter_of_frontier_subset_interior hR hBP, hS,
    Set.frontier_inter_subset_interior_of_frontier_subset_interior hBP,
    Set.disjoint_frontier_inter_of_frontier_subset_interior hBP,
    Set.frontier_inter_of_frontier_subset_interior hP.isClosed hR.closed hBP,
    ?_, ?_, hDS, ?_⟩
  · intro x hx
    exact ⟨interior_subset (hZP (Or.inl (Or.inl hx))), hAR hx⟩
  · rw [hpreK, Set.interior_subtype_preimage_of_frontier_subset_interior hBP]
    intro x hx
    exact hZP (Or.inl hx)
  · rw [hpreK, Set.frontier_subtype_preimage_of_frontier_subset_interior hP.isClosed hBP]
    ext x
    exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩
  · intro x p hp
    apply hloops x p
    intro t htD
    exact disjoint_left.mp hDS (mem_image_of_mem Subtype.val htD) (hp t)

end PoincareMT.M76
