import PoincareLib.Topology.Manifold.NeckCap.Cap.Projective.BoundaryLift

/-!
# The compact lifted core of a projective cap

The specified closed core lifts to a compact subset of the standard
three-sphere. Open-map identities identify its interior with the lifted
core interior. Compactness excludes the puncture fiber from its closure,
so its ambient frontier is precisely the two lifted boundary spheres.

Reference: Morgan--Tian, Definition 9.72, pp. 230--231.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)
  (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)

/-- The actual closed core lifted into the standard three-sphere, with the
two points over the original puncture excluded. -/
def projectiveClosedCoreLift : Set UnitThreeSphere :=
  {q | Quotient.mk' q ≠ C.puncture ∧ S.cover q ∈ C.closed_core}

theorem isCompact_projectiveClosedCoreLift : IsCompact (C.projectiveClosedCoreLift S) :=
  S.isCompact_lift C.closed_core_compact C.closed_core_subset_carrier

/-- Interior is computed in the ambient three-sphere, not merely in the
punctured covering space. -/
theorem interior_projectiveClosedCoreLift :
    interior (C.projectiveClosedCoreLift S) =
      {q : UnitThreeSphere | Quotient.mk' q ≠ C.puncture ∧ S.cover q ∈ C.core} := by
  let v : PuncturedProjectiveSphere C.puncture → UnitThreeSphere := Subtype.val
  let f : PuncturedProjectiveSphere C.puncture → M :=
    fun q => S.cover q
  have hv : IsLocalHomeomorph v :=
    (isOpen_puncturedProjectiveSphere C.puncture).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hf : IsLocalHomeomorph f :=
    C.carrier_open.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
      S.restrictedCover_isLocalHomeomorph
  have hpre : v ⁻¹' C.projectiveClosedCoreLift S = f ⁻¹' C.closed_core := by
    ext q
    exact and_iff_right q.property
  have hi : v ⁻¹' interior (C.projectiveClosedCoreLift S) =
      f ⁻¹' interior C.closed_core := by
    rw [hv.isOpenMap.preimage_interior_eq_interior_preimage hv.continuous, hpre,
      ← hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous]
  have hiff (q : UnitThreeSphere) (hq : Quotient.mk' q ≠ C.puncture) :
      q ∈ interior (C.projectiveClosedCoreLift S) ↔ S.cover q ∈ C.core := by
    have h := Set.ext_iff.mp hi (⟨q, hq⟩ : PuncturedProjectiveSphere C.puncture)
    change q ∈ interior (C.projectiveClosedCoreLift S) ↔
      S.cover q ∈ interior C.closed_core at h
    rwa [← C.core_eq_interior_closed_core] at h
  ext q
  constructor
  · intro hq
    have hp : Quotient.mk' q ≠ C.puncture := (interior_subset hq).1
    exact ⟨hp, (hiff q hp).mp hq⟩
  · rintro ⟨hp, hq⟩
    exact (hiff q hp).mpr hq

/-- Compactness ensures that the deleted puncture points contribute no
additional frontier to the lifted closed core. -/
theorem frontier_projectiveClosedCoreLift :
    frontier (C.projectiveClosedCoreLift S) =
      {q : UnitThreeSphere |
        Quotient.mk' q ≠ C.puncture ∧ S.cover q ∈ C.boundary_sphere} := by
  rw [frontier, (C.isCompact_projectiveClosedCoreLift S).isClosed.closure_eq,
    C.interior_projectiveClosedCoreLift S, C.boundary_eq_closed_core_diff_core]
  ext q
  simp only [projectiveClosedCoreLift, mem_sdiff, mem_ofPred_eq]
  tauto

/-- The ambient frontier of the actual compact lifted core consists exactly
of the two disjoint antipodal smooth sphere lifts of its boundary neck. -/
theorem exists_projectiveClosedCoreLift_frontier_spheres :
    ∃ F : UnitTwoSphere → UnitThreeSphere,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F ∧
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => -F q) ∧
      (∀ q, Quotient.mk' (F q) ≠ C.puncture) ∧
      (∀ q, S.cover (F q) = C.boundary_neck.coordinate_map (q, 0)) ∧
      Disjoint (range F) (range (fun q => -F q)) ∧
      frontier (C.projectiveClosedCoreLift S) = range F ∪ range (fun q => -F q) := by
  rw [C.frontier_projectiveClosedCoreLift S]
  exact C.exists_boundary_sphere_lift S

/-- The original projective cap model supplies a compact lifted core whose
interior and two smooth frontier components agree with the actual cap data. -/
theorem exists_projective_core_lift (hkind : C.model_kind = .puncturedProjective) :
    ∃ S : StandardPuncturedProjectiveCover M C.puncture C.carrier,
      IsCompact (C.projectiveClosedCoreLift S) ∧
      interior (C.projectiveClosedCoreLift S) =
        {q : UnitThreeSphere | Quotient.mk' q ≠ C.puncture ∧ S.cover q ∈ C.core} ∧
      ∃ F : UnitTwoSphere → UnitThreeSphere,
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F ∧
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => -F q) ∧
        (∀ q, Quotient.mk' (F q) ≠ C.puncture) ∧
        (∀ q, S.cover (F q) = C.boundary_neck.coordinate_map (q, 0)) ∧
        Disjoint (range F) (range (fun q => -F q)) ∧
        frontier (C.projectiveClosedCoreLift S) = range F ∪ range (fun q => -F q) := by
  obtain ⟨S⟩ := C.nonempty_projective_cover hkind
  exact ⟨S, C.isCompact_projectiveClosedCoreLift S, C.interior_projectiveClosedCoreLift S,
    C.exists_projectiveClosedCoreLift_frontier_spheres S⟩

end PoincareMT.CapCertificate
