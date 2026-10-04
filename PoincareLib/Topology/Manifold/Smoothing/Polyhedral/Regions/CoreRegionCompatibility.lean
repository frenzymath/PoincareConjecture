import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CoreProjectionCoordinates

/-!
# Agreement of box extensions on overlapping regions

The intersection face controls an overlap. Projection to either
larger core stays in that face's region, and nested projection
compatibility preserves its core base. Fields already constant
along the smaller boxes therefore agree at the overlap point and
the new core base. See Cairns 1940, pp. 803--805, and M76
derivation 45.
-/

set_option autoImplicit false

open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι]

/-- A face region with the strict global threshold bound has a
nonempty face label. See Cairns p. 803 and M76 derivation 45. -/
theorem nonempty_of_mem_faceRegion {s : Finset ι} {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ}
    (hq : q ∈ faceRegion s η) : s.Nonempty := by
  have hm := residualMass_pos_of_mem_faceRegion s hη hbound ⟨q, hq⟩
  change 0 < residualMass s η q at hm
  by_contra hs
  rw [Finset.not_nonempty_iff_eq_empty.mp hs, residualMass, Finset.sum_empty] at hm
  exact (lt_irrefl (0 : ℝ)) hm

variable [DecidableEq ι]

/-- A point common to two face regions also belongs to their
intersection face's region. See Cairns p. 803 and M76 derivation 45. -/
theorem mem_faceRegion_inter {s t : Finset ι} {η : ℝ} {q : ι → ℝ}
    (hs : q ∈ faceRegion s η) (ht : q ∈ faceRegion t η) :
    q ∈ faceRegion (s ∩ t) η := by
  refine ⟨hs.1, fun i hi => hs.2.1 i (Finset.mem_inter.mp hi).1, fun i hi => ?_⟩
  by_cases his : i ∈ s
  · exact ht.2.2 i (fun hit => hi (Finset.mem_inter.mpr ⟨his, hit⟩))
  · exact hs.2.2 i his

/-- On an overlap with a nested smaller face, projection to the
larger core stays in the smaller face region.
See Cairns pp. 803--805 and M76 derivation 45. -/
theorem projectToFace_mem_faceRegion_of_subset {r s : Finset ι} (hrs : r ⊆ s)
    {η : ℝ} (hη : 0 ≤ η) (hbound : (Fintype.card ι : ℝ) * η < 1)
    {q : ι → ℝ} (hs : q ∈ faceRegion s η) (hr : q ∈ faceRegion r η) :
    projectToFace s η q ∈ faceRegion r η := by
  have hcore := projectToFace_mem_core s hη hbound ⟨q, hs⟩
  refine ⟨projectToFace_mem_stdSimplex s hη hbound ⟨q, hs⟩,
    fun i hi => hcore.1 ⟨i, hrs hi⟩, fun i hi => ?_⟩
  by_cases his : i ∈ s
  · have he := coordinate_eq_of_mem_faceRegions hs hr his hi
    simp only [projectToFace, if_pos his, he, sub_self, zero_mul, zero_div, add_zero, le_refl]
  · simpa only [projectToFace, if_neg his] using hη

/-- Nested core projections compose for region points; their
required positivity follows from the region hypotheses.
See Cairns pp. 803--805 and M76 derivation 45. -/
theorem projectToFace_projectToFace_of_mem_faceRegions {r s : Finset ι} (hrs : r ⊆ s)
    {η : ℝ} (hη : 0 ≤ η) (hbound : (Fintype.card ι : ℝ) * η < 1)
    {q : ι → ℝ} (hs : q ∈ faceRegion s η) (hr : q ∈ faceRegion r η) :
    projectToFace r η (projectToFace s η q) = projectToFace r η q := by
  apply projectToFace_projectToFace hrs η q
  · simpa only [Fintype.card_coe] using (sub_pos.mpr (face_threshold_bound s hη hbound)).ne'
  · exact (residualMass_pos_of_mem_faceRegion r hη hbound ⟨q, hr⟩).ne'
  · exact (residualMass_pos_of_mem_faceRegion s hη hbound ⟨q, hs⟩).ne'

/-- Constancy on the intersection face's boxes makes the old
field agree at an overlap point and the new core base. No topology
on the target is needed for this exact identity.
See Cairns pp. 803--805 and M76 derivation 45. -/
theorem field_eq_at_coreBase_of_overlap {Y : Type*} {s t : Finset ι}
    {η : ℝ} (hη : 0 ≤ η) (hbound : (Fintype.card ι : ℝ) * η < 1)
    (f : (ι → ℝ) → Y)
    (hf : ∀ z ∈ faceRegion (s ∩ t) η, f z = f (projectToFace (s ∩ t) η z))
    {q : ι → ℝ} (hs : q ∈ faceRegion s η) (ht : q ∈ faceRegion t η) :
    f (projectToFace s η q) = f q := by
  have hr := mem_faceRegion_inter hs ht
  have hp := projectToFace_mem_faceRegion_of_subset Finset.inter_subset_left hη hbound hs hr
  rw [hf _ hp, projectToFace_projectToFace_of_mem_faceRegions
    Finset.inter_subset_left hη hbound hs hr, ← hf q hr]

end StdSimplexCore
