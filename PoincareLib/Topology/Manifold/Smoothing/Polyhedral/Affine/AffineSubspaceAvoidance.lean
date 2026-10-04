import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# Paths avoiding affine subspaces of codimension at least two

Inside a convex open set, a generic intermediate point gives two
segments avoiding finitely many smaller affine subspaces. This
supports local polyhedral projection coverage in Cairns 1940,
pp. 804--806; see M76 derivation 67.
-/

set_option autoImplicit false

open Set AffineMap Module

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A proper affine subspace has dense complement. See Cairns
pp. 804--806 and the general-position argument in M76 derivation 67. -/
theorem dense_compl_of_ne_top (A : AffineSubspace ℝ E) (hA : A ≠ ⊤) :
    Dense (A : Set E)ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  by_contra h
  have htop := isOpen_interior.affineSpan_eq_top (Set.nonempty_iff_ne_empty.mpr h)
  have hle : affineSpan ℝ (interior (A : Set E)) ≤ A := affineSpan_le.mpr interior_subset
  exact hA (top_le_iff.mp (htop ▸ hle))

/-- A segment avoids an affine subspace if its first endpoint
misses the subspace and its second endpoint misses the span with
the first endpoint adjoined. See Cairns pp. 804--806 and M76 derivation 67. -/
theorem segment_subset_compl_of_notMem_span_insert (A : AffineSubspace ℝ E)
    {x z : E} (hx : x ∉ A) (hz : z ∉ affineSpan ℝ (insert x (A : Set E))) :
    segment ℝ x z ⊆ (A : Set E)ᶜ := by
  rw [segment_eq_image_lineMap]
  rintro _ ⟨t, _, rfl⟩ htA
  change lineMap x z t ∈ A at htA
  by_cases ht : t = 0
  · exact hx (by simpa only [ht, lineMap_apply_zero] using htA)
  · apply hz
    have hline := lineMap_mem (Q := affineSpan ℝ (insert x (A : Set E))) t⁻¹
      (subset_affineSpan ℝ _ (mem_insert x _))
      (subset_affineSpan ℝ _ (mem_insert_of_mem _ htA))
    simpa only [lineMap_lineMap_right, inv_mul_cancel₀ ht, lineMap_apply_one] using hline

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Adjoining one point to an affine subspace of codimension at
least two leaves a proper affine subspace. See Cairns pp. 804--806
and M76 derivation 67. -/
theorem span_insert_ne_top_of_finrank_lt (A : AffineSubspace ℝ E)
    (hA : Module.finrank ℝ A.direction + 1 < Module.finrank ℝ E) (x : E) :
    affineSpan ℝ (insert x (A : Set E)) ≠ ⊤ := by
  intro he
  have h := finrank_vectorSpan_insert_le A x
  rw [← direction_affineSpan, he, direction_top, finrank_top] at h
  omega

/-- The complement of finitely many proper affine subspaces is
dense. See Cairns pp. 804--806 and M76 derivation 67. -/
theorem dense_compl_iUnion {ι : Type*} [Finite ι] (A : ι → AffineSubspace ℝ E)
    (hA : ∀ i, A i ≠ ⊤) : Dense (⋃ i, (A i : Set E))ᶜ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [compl_iUnion]
  exact dense_iInter_of_isOpen (fun i => (A i).closed_of_finiteDimensional.isOpen_compl)
    (fun i => (A i).dense_compl_of_ne_top (hA i))

/-- Removing finitely many affine subspaces of codimension at
least two from a nonempty convex open set leaves a path-connected
set. See Cairns pp. 804--806 and M76 derivation 67. -/
theorem isPathConnected_sdiff_iUnion {ι : Type*} [Finite ι]
    (A : ι → AffineSubspace ℝ E)
    (hA : ∀ i, Module.finrank ℝ (A i).direction + 1 < Module.finrank ℝ E)
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hne : U.Nonempty) :
    IsPathConnected (U \ ⋃ i, (A i : Set E)) := by
  have hproper : ∀ i, A i ≠ ⊤ := by
    intro i he
    have hi := hA i
    rw [he, direction_top, finrank_top] at hi
    omega
  obtain ⟨x, hxU, hxA⟩ := (dense_compl_iUnion A hproper).inter_open_nonempty U hU hne
  refine ⟨x, ⟨hxU, hxA⟩, ?_⟩
  intro y hy
  let B : Bool × ι → AffineSubspace ℝ E := fun j =>
    affineSpan ℝ (insert (if j.1 then x else y) (A j.2 : Set E))
  have hB : ∀ j, B j ≠ ⊤ := fun j =>
    (A j.2).span_insert_ne_top_of_finrank_lt (hA j.2) _
  obtain ⟨z, hzU, hzB⟩ := (dense_compl_iUnion B hB).inter_open_nonempty U hU hne
  have hz (b : Bool) (i : ι) : z ∉ B (b, i) := fun hi => hzB (mem_iUnion.mpr ⟨(b, i), hi⟩)
  have hsegx : segment ℝ x z ⊆ U \ ⋃ i, (A i : Set E) := by
    intro w hw
    refine ⟨hconv.segment_subset hxU hzU hw, ?_⟩
    intro hwA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hwA
    exact (A i).segment_subset_compl_of_notMem_span_insert
      (fun h => hxA (mem_iUnion.mpr ⟨i, h⟩)) (hz true i) hw hi
  have hsegy : segment ℝ y z ⊆ U \ ⋃ i, (A i : Set E) := by
    intro w hw
    refine ⟨hconv.segment_subset hy.1 hzU hw, ?_⟩
    intro hwA
    obtain ⟨i, hi⟩ := mem_iUnion.mp hwA
    exact (A i).segment_subset_compl_of_notMem_span_insert
      (fun h => hy.2 (mem_iUnion.mpr ⟨i, h⟩)) (hz false i) hw hi
  exact (JoinedIn.of_segment_subset hsegx).trans (JoinedIn.of_segment_subset hsegy).symm

end AffineSubspace
