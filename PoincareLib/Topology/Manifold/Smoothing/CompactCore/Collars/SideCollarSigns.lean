import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.TwoCollarGluing

/-!
# The complete side equations of the actual glued collar

Injectivity and the entire fixed base identify exactly the zero
height. The original positive and negative collar ranges then give
both full sign equivalences. See Wall derivation006, section4.
-/

set_option autoImplicit false

open Set BrownCollar

namespace BrownCollar.AmbientSideCollars

variable {X : Type*} [TopologicalSpace X] {S : Set X} (C : AmbientSideCollars S)

/-- The full original base has exactly zero height in the actual
glued bicollar. See Wall006, section4. -/
theorem bicollar_mem_base_iff (z : S × Ioo (-1 : ℝ) 1) :
    (C.bicollarHomeomorph z : X) ∈ S ↔ (z.2 : ℝ) = 0 := by
  constructor
  · intro hz
    let s : S := ⟨C.bicollarHomeomorph z, hz⟩
    have heq : C.bicollarHomeomorph z = C.bicollarHomeomorph (bicollarBase s) :=
      Subtype.ext (C.bicollarHomeomorph_base s).symm
    exact congrArg (fun w : S × Ioo (-1 : ℝ) 1 => (w.2 : ℝ))
      (C.bicollarHomeomorph.injective heq)
  · intro hz
    have heq : z = bicollarBase z.1 := Prod.ext rfl (Subtype.ext hz)
    rw [heq, C.bicollarHomeomorph_base]
    exact z.1.property

private theorem bicollar_mem_positive_of_nonneg (z : S × Ioo (-1 : ℝ) 1)
    (hz : 0 ≤ (z.2 : ℝ)) : (C.bicollarHomeomorph z : X) ∈ C.positive := by
  change (C.gluedCollar z : X) ∈ C.positive
  rw [gluedCollar, if_pos hz]
  exact C.positiveImage_subset (C.positiveImageHomeomorph (positiveClamp z)).property

private theorem bicollar_mem_negative_of_nonpos (z : S × Ioo (-1 : ℝ) 1)
    (hz : (z.2 : ℝ) ≤ 0) : (C.bicollarHomeomorph z : X) ∈ C.negative := by
  have heq : C.gluedCollar z = C.negativeUnionMap (negativeClamp z) := by
    rw [← C.gluedCollar_negativeHalfInclusion,
      negativeHalfInclusion_negativeClamp z hz]
  change (C.gluedCollar z : X) ∈ C.negative
  rw [heq]
  exact C.negativeImage_subset (C.negativeImageHomeomorph (negativeClamp z)).property

/-- The actual positive domain is precisely nonnegative height on
the complete glued cylinder. See Wall006, section4. -/
theorem bicollar_mem_positive_iff (z : S × Ioo (-1 : ℝ) 1) :
    (C.bicollarHomeomorph z : X) ∈ C.positive ↔ 0 ≤ (z.2 : ℝ) := by
  refine ⟨?_, C.bicollar_mem_positive_of_nonneg z⟩
  intro hp
  by_contra hz
  have hm := C.bicollar_mem_negative_of_nonpos z (le_of_lt (lt_of_not_ge hz))
  have hbase : (C.bicollarHomeomorph z : X) ∈ S := C.inter_eq.subset ⟨hp, hm⟩
  have ht := (C.bicollar_mem_base_iff z).mp hbase
  rw [ht] at hz
  exact hz le_rfl

/-- The actual negative domain is precisely nonpositive height on
the complete glued cylinder. See Wall006, section4. -/
theorem bicollar_mem_negative_iff (z : S × Ioo (-1 : ℝ) 1) :
    (C.bicollarHomeomorph z : X) ∈ C.negative ↔ (z.2 : ℝ) ≤ 0 := by
  refine ⟨?_, C.bicollar_mem_negative_of_nonpos z⟩
  intro hm
  by_contra hz
  have hp := C.bicollar_mem_positive_of_nonneg z (le_of_lt (lt_of_not_ge hz))
  have hbase : (C.bicollarHomeomorph z : X) ∈ S := C.inter_eq.subset ⟨hp, hm⟩
  have ht := (C.bicollar_mem_base_iff z).mp hbase
  rw [ht] at hz
  exact hz le_rfl

end BrownCollar.AmbientSideCollars
