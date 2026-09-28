import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

open Set
open scoped ENNReal

universe u v

namespace MeasureTheory.Measure

theorem comap_hausdorffMeasure_of_locally_isometry
    {X : Type u} {Y : Type v} [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology X] {f : X → Y} (hf : MeasurableEmbedding f)
    {d : ℝ} (hd : 0 ≤ d)
    (hlocal : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, ∀ z ∈ W, edist (f y) (f z) = edist y z) :
    (hausdorffMeasure d : Measure Y).comap f =
      (hausdorffMeasure d : Measure X) := by
  classical
  choose W hWopen hxW hdist using hlocal
  obtain ⟨s, hs, hcover⟩ := isLindelof_univ.elim_countable_subcover W hWopen
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  apply ext_of_biUnion_eq_univ hs (univ_subset_iff.mp hcover)
  intro x _
  ext A hA
  rw [restrict_apply hA, restrict_apply hA,
    comap_apply f hf.injective (fun S hS => hf.measurableSet_image.mpr hS)
      _ (hA.inter (hWopen x).measurableSet)]
  have hi : Isometry (fun y : W x => f y) := fun y z =>
    hdist x y y.property z z.property
  let B : Set (W x) := (Subtype.val : W x → X) ⁻¹' A
  have himage : (Subtype.val : W x → X) '' B = A ∩ W x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.property⟩
    · intro hy
      exact ⟨⟨y, hy.2⟩, hy.1, rfl⟩
  have himagef : (fun y : W x => f y) '' B = f '' (A ∩ W x) := by
    rw [← himage, image_image]
  rw [← himagef, hi.hausdorffMeasure_image (Or.inl hd), ← himage,
    isometry_subtype_coe.hausdorffMeasure_image (Or.inl hd)]

end MeasureTheory.Measure
