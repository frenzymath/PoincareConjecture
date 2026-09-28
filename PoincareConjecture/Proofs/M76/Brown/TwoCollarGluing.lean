import PoincareConjecture.Proofs.M76.Brown.CollarUnionNeighborhood
import PoincareConjecture.Proofs.M76.Brown.SignedCylinderCoordinates

set_option autoImplicit false

open Set

namespace BrownCollar.AmbientSideCollars

variable {X : Type*} [TopologicalSpace X] {S : Set X} (C : AmbientSideCollars S)

noncomputable def gluedCollar : S × Ioo (-1 : ℝ) 1 → C.collarUnion := fun z =>
  if 0 ≤ (z.2 : ℝ) then C.positiveUnionMap (positiveClamp z)
  else C.negativeUnionMap (negativeClamp z)

theorem continuous_gluedCollar : Continuous C.gluedCollar := by
  apply continuous_if_le continuous_const (continuous_subtype_val.comp continuous_snd)
    (C.isClosedEmbedding_positiveUnionMap.continuous.comp continuous_positiveClamp).continuousOn
    (C.isClosedEmbedding_negativeUnionMap.continuous.comp continuous_negativeClamp).continuousOn
  intro z hz
  change C.positiveUnionMap (positiveClamp z) = C.negativeUnionMap (negativeClamp z)
  rw [positiveClamp_of_zero z hz.symm, negativeClamp_of_zero z hz.symm]
  apply Subtype.ext
  rw [C.positiveUnionMap_base, C.negativeUnionMap_base]

theorem gluedCollar_positiveHalfInclusion (z : S × Ico (0 : ℝ) 1) :
    C.gluedCollar (positiveHalfInclusion z) = C.positiveUnionMap z := by
  have hz : 0 ≤ ((positiveHalfInclusion z).2 : ℝ) := z.2.property.1
  rw [gluedCollar, if_pos hz, positiveClamp_positiveHalfInclusion]

theorem gluedCollar_base (s : S) : (C.gluedCollar (bicollarBase s) : X) = (s : X) := by
  rw [← positiveHalfInclusion_base, C.gluedCollar_positiveHalfInclusion]
  exact C.positiveUnionMap_base s

theorem gluedCollar_negativeHalfInclusion (z : S × Ico (0 : ℝ) 1) :
    C.gluedCollar (negativeHalfInclusion z) = C.negativeUnionMap z := by
  by_cases hz0 : (z.2 : ℝ) = 0
  · have hzbase : z = collarBase z.1 := Prod.ext rfl (Subtype.ext hz0)
    have hzinc : negativeHalfInclusion z = bicollarBase z.1 := by
      rw [hzbase, negativeHalfInclusion_base]
      rfl
    apply Subtype.ext
    rw [hzinc, C.gluedCollar_base, hzbase, C.negativeUnionMap_base]
    rfl
  · have hz : ¬0 ≤ ((negativeHalfInclusion z).2 : ℝ) := by
      change ¬0 ≤ -(z.2 : ℝ)
      have hpos : 0 < (z.2 : ℝ) := lt_of_le_of_ne z.2.property.1 (Ne.symm hz0)
      linarith
    rw [gluedCollar, if_neg hz, negativeClamp_negativeHalfInclusion]

theorem equal_opposite_collar_points (u v : S × Ico (0 : ℝ) 1)
    (h : C.positiveUnionMap u = C.negativeUnionMap v) :
    ∃ s : S, u = collarBase s ∧ v = collarBase s := by
  have hp : (C.positiveUnionMap u : X) ∈ C.positiveImage :=
    (C.positiveImageHomeomorph u).property
  have hm : (C.positiveUnionMap u : X) ∈ C.negativeImage := by
    rw [h]
    exact (C.negativeImageHomeomorph v).property
  let s : S := ⟨C.positiveUnionMap u, C.images_inter.subset ⟨hp, hm⟩⟩
  have heq : C.positiveUnionMap u = C.positiveUnionMap (collarBase s) :=
    Subtype.ext (C.positiveUnionMap_base s).symm
  have hb : C.positiveUnionMap (collarBase s) = C.negativeUnionMap (collarBase s) := by
    apply Subtype.ext
    rw [C.positiveUnionMap_base, C.negativeUnionMap_base]
  exact ⟨s, C.isClosedEmbedding_positiveUnionMap.injective heq,
    C.isClosedEmbedding_negativeUnionMap.injective (h.symm.trans (heq.trans hb))⟩

theorem gluedCollar_injective : Function.Injective C.gluedCollar := by
  have hcross (a b : S × Ioo (-1 : ℝ) 1) (ha : 0 ≤ (a.2 : ℝ))
      (hb : (b.2 : ℝ) ≤ 0)
      (heq : C.positiveUnionMap (positiveClamp a) = C.negativeUnionMap (negativeClamp b)) :
      a = b := by
    obtain ⟨s, hpa, hmb⟩ := C.equal_opposite_collar_points _ _ heq
    calc
      a = positiveHalfInclusion (positiveClamp a) :=
        (positiveHalfInclusion_positiveClamp a ha).symm
      _ = positiveHalfInclusion (collarBase s) := congrArg positiveHalfInclusion hpa
      _ = negativeHalfInclusion (collarBase s) := by
        rw [positiveHalfInclusion_base, negativeHalfInclusion_base]
      _ = negativeHalfInclusion (negativeClamp b) := congrArg negativeHalfInclusion hmb.symm
      _ = b := negativeHalfInclusion_negativeClamp b hb
  intro a b h
  by_cases ha : 0 ≤ (a.2 : ℝ)
  · by_cases hb : 0 ≤ (b.2 : ℝ)
    · simp only [gluedCollar, if_pos ha, if_pos hb] at h
      have heq := C.isClosedEmbedding_positiveUnionMap.injective h
      have hin := congrArg positiveHalfInclusion heq
      simpa only [positiveHalfInclusion_positiveClamp a ha,
        positiveHalfInclusion_positiveClamp b hb] using hin
    · simp only [gluedCollar, if_pos ha, if_neg hb] at h
      exact hcross a b ha (le_of_lt (lt_of_not_ge hb)) h
  · by_cases hb : 0 ≤ (b.2 : ℝ)
    · simp only [gluedCollar, if_neg ha, if_pos hb] at h
      exact (hcross b a hb (le_of_lt (lt_of_not_ge ha)) h.symm).symm
    · simp only [gluedCollar, if_neg ha, if_neg hb] at h
      have heq := C.isClosedEmbedding_negativeUnionMap.injective h
      have hin := congrArg negativeHalfInclusion heq
      simpa only [negativeHalfInclusion_negativeClamp a (le_of_lt (lt_of_not_ge ha)),
        negativeHalfInclusion_negativeClamp b (le_of_lt (lt_of_not_ge hb))] using hin

theorem gluedCollar_surjective : Function.Surjective C.gluedCollar := by
  intro y
  rcases y.property with hp | hm
  · let yp : C.positiveImage := ⟨y.val, hp⟩
    refine ⟨positiveHalfInclusion (C.positiveImageHomeomorph.symm yp), ?_⟩
    rw [C.gluedCollar_positiveHalfInclusion]
    apply Subtype.ext
    change (C.positiveImageHomeomorph (C.positiveImageHomeomorph.symm yp) : X) = y.val
    exact congrArg Subtype.val (C.positiveImageHomeomorph.apply_symm_apply yp)
  · let ym : C.negativeImage := ⟨y.val, hm⟩
    refine ⟨negativeHalfInclusion (C.negativeImageHomeomorph.symm ym), ?_⟩
    rw [C.gluedCollar_negativeHalfInclusion]
    apply Subtype.ext
    change (C.negativeImageHomeomorph (C.negativeImageHomeomorph.symm ym) : X) = y.val
    exact congrArg Subtype.val (C.negativeImageHomeomorph.apply_symm_apply ym)

theorem gluedCollar_image (F : Set (S × Ioo (-1 : ℝ) 1)) :
    C.gluedCollar '' F =
      C.positiveUnionMap '' (positiveHalfInclusion ⁻¹' F) ∪
      C.negativeUnionMap '' (negativeHalfInclusion ⁻¹' F) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    by_cases ht : 0 ≤ (z.2 : ℝ)
    · refine Or.inl ⟨positiveClamp z, ?_, ?_⟩
      · change positiveHalfInclusion (positiveClamp z) ∈ F
        rwa [positiveHalfInclusion_positiveClamp z ht]
      · rw [gluedCollar, if_pos ht]
    · refine Or.inr ⟨negativeClamp z, ?_, ?_⟩
      · change negativeHalfInclusion (negativeClamp z) ∈ F
        rwa [negativeHalfInclusion_negativeClamp z (le_of_lt (lt_of_not_ge ht))]
      · rw [gluedCollar, if_neg ht]
  · rintro (hy | hy)
    · rcases hy with ⟨z, hz, heq⟩
      refine ⟨positiveHalfInclusion z, hz, ?_⟩
      rw [C.gluedCollar_positiveHalfInclusion]
      exact heq
    · rcases hy with ⟨z, hz, heq⟩
      refine ⟨negativeHalfInclusion z, hz, ?_⟩
      rw [C.gluedCollar_negativeHalfInclusion]
      exact heq

theorem isClosedMap_gluedCollar : IsClosedMap C.gluedCollar := by
  intro F hF
  rw [C.gluedCollar_image]
  exact (C.isClosedEmbedding_positiveUnionMap.isClosedMap _
    (hF.preimage continuous_positiveHalfInclusion)).union
      (C.isClosedEmbedding_negativeUnionMap.isClosedMap _
        (hF.preimage continuous_negativeHalfInclusion))

noncomputable def bicollarHomeomorph : (S × Ioo (-1 : ℝ) 1) ≃ₜ C.collarUnion :=
  (Equiv.ofBijective C.gluedCollar
    ⟨C.gluedCollar_injective, C.gluedCollar_surjective⟩).toHomeomorphOfContinuousClosed
      C.continuous_gluedCollar C.isClosedMap_gluedCollar

theorem bicollarHomeomorph_base (s : S) :
    (C.bicollarHomeomorph (bicollarBase s) : X) = (s : X) := C.gluedCollar_base s

end BrownCollar.AmbientSideCollars
