import PoincareLib.Topology.Manifold.Surgery.Event.Shared.SharedCutPatches

/-!
# The actual map between shared regions of successive cuts

Compatible Euclidean patches glue to an open embedding from their literal
union in the larger capped carrier into the smaller capped carrier. The
map retains every prescribed old point and shared signed ball coordinate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S R : Set (Fin (F.event T hT).cap_count)) (hSR : S ⊆ R)

/-- The literal union of the larger old domain and all shared full ball patches. -/
noncomputable def sharedCutOpen : TopologicalSpace.Opens (partialCappedCarrier F T hT P R).carrier :=
  ⟨⋃ j, Set.range (sharedCutInclude F T hT P S R hSR j),
    isOpen_iUnion (fun j => (sharedCutInclude_openEmbedding F T hT P S R hSR j).isOpen_range)⟩

/-- All shared patches glue to an actual open embedding, including for empty selections. -/
theorem exists_sharedCutComparison :
    ∃ f : sharedCutOpen F T hT P S R hSR → (partialCappedCarrier F T hT P S).carrier,
      IsOpenEmbedding f ∧ ∀ j (x : sharedCutDomain F T hT P S R hSR j),
        f ⟨sharedCutInclude F T hT P S R hSR j x,
          Set.mem_iUnion.mpr ⟨j, Set.mem_range_self x⟩⟩ = sharedCutPatch F T hT P S R hSR j x :=
  Poincare.Gluing.exists_isOpenEmbedding_iUnion_ranges
    (sharedCutInclude_openEmbedding F T hT P S R hSR)
    (sharedCutPatch_openEmbedding F T hT P S R hSR) (sharedCutPatch_eq_iff F T hT P S R hSR)

/-- The comparison selected from the exact compatible-patch construction. -/
noncomputable def sharedCutComparison :
    sharedCutOpen F T hT P S R hSR → (partialCappedCarrier F T hT P S).carrier :=
  Classical.choose (exists_sharedCutComparison F T hT P S R hSR)

/-- The actual comparison embeds its inherited open domain openly. -/
theorem sharedCutComparison_openEmbedding :
    IsOpenEmbedding (sharedCutComparison F T hT P S R hSR) :=
  (Classical.choose_spec (exists_sharedCutComparison F T hT P S R hSR)).1

/-- The chosen map agrees with each literal old or shared ball patch. -/
theorem sharedCutComparison_patch (j : SharedCutIndex F T hT P S R)
    (x : sharedCutDomain F T hT P S R hSR j) :
    sharedCutComparison F T hT P S R hSR
      ⟨sharedCutInclude F T hT P S R hSR j x, Set.mem_iUnion.mpr ⟨j, Set.mem_range_self x⟩⟩ =
        sharedCutPatch F T hT P S R hSR j x :=
  (Classical.choose_spec (exists_sharedCutComparison F T hT P S R hSR)).2 j x

/-- The comparison image is precisely the union of the prescribed target patch images. -/
theorem sharedCutComparison_range :
    Set.range (sharedCutComparison F T hT P S R hSR) =
      ⋃ j, Set.range (sharedCutPatch F T hT P S R hSR j) := by
  apply Set.Subset.antisymm
  · rintro q ⟨x, rfl⟩
    obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp x.property
    have hx : x = ⟨sharedCutInclude F T hT P S R hSR j z,
        Set.mem_iUnion.mpr ⟨j, Set.mem_range_self z⟩⟩ := Subtype.ext hz.symm
    rw [hx, sharedCutComparison_patch]
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_range_self z⟩
  · intro q hq
    obtain ⟨j, z, rfl⟩ := Set.mem_iUnion.mp hq
    exact ⟨⟨sharedCutInclude F T hT P S R hSR j z,
      Set.mem_iUnion.mpr ⟨j, Set.mem_range_self z⟩⟩,
        sharedCutComparison_patch F T hT P S R hSR j z⟩

/-- Every actual old point belongs to the shared source domain. -/
theorem partialOldInclusion_mem_shared (y : eventCutOpen F T hT P R) :
    partialOldInclusion F T hT P R y ∈ sharedCutOpen F T hT P S R hSR := by
  let x : partialCappingDomain F T hT P R (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  refine Set.mem_iUnion.mpr ⟨Sum.inl y, x, ?_⟩
  change partialCappingInclude F T hT P R (.inl y) x = _
  rw [← partialOldInclusion_patch, partialCappingMap_old_center]

/-- The comparison keeps the actual pre-surgery point on the whole old domain. -/
theorem sharedCutComparison_old (y : eventCutOpen F T hT P R) :
    sharedCutComparison F T hT P S R hSR
      ⟨partialOldInclusion F T hT P R y, partialOldInclusion_mem_shared F T hT P S R hSR y⟩ =
        partialOldInclusion F T hT P S (successiveOldInclusion F T hT P S R hSR y) := by
  let x : partialCappingDomain F T hT P R (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  have hx := sharedCutComparison_patch F T hT P S R hSR (.inl y) x
  have heq : sharedCutInclude F T hT P S R hSR (.inl y) x =
      partialOldInclusion F T hT P R y := by
    change partialCappingInclude F T hT P R (.inl y) x = _
    rw [← partialOldInclusion_patch, partialCappingMap_old_center]
  have hsource : (⟨sharedCutInclude F T hT P S R hSR (.inl y) x,
      Set.mem_iUnion.mpr ⟨Sum.inl y, Set.mem_range_self x⟩⟩ : sharedCutOpen F T hT P S R hSR) =
      ⟨partialOldInclusion F T hT P R y, partialOldInclusion_mem_shared F T hT P S R hSR y⟩ :=
    Subtype.ext heq
  rw [hsource] at hx
  change _ = partialOldInclusion F T hT P S
    (successiveOldInclusion F T hT P S R hSR (partialCappingMap F T hT P R (.inl y) x)) at hx
  rwa [partialCappingMap_old_center] at hx

/-- The comparison keeps all coordinates of every shared signed cap patch. -/
theorem sharedCutComparison_cap (a : S × Bool) (x : capDoubleBall) :
    sharedCutComparison F T hT P S R hSR
      ⟨partialCappingInclude F T hT P R (.inr (successiveCapIndex F T hT S R hSR a)) x,
        Set.mem_iUnion.mpr ⟨Sum.inr a, Set.mem_range_self x⟩⟩ =
          partialCappingInclude F T hT P S (.inr a) x :=
  sharedCutComparison_patch F T hT P S R hSR (.inr a) x

end PoincareMT.M38
