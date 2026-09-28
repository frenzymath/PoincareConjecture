import PoincareConjecture.Proofs.M76.Wall.BicollarBaseRestriction








set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S C K R : Set X}




theorem exists_bicollar_in_domain
    (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C) (hCR : C ⊆ R)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X))
    (hside : ∀ z, (H z : X) ∈ K ↔ 0 ≤ (z.2 : ℝ)) :
    ∃ G : (((Subtype.val : R → X) ⁻¹' S) × Ioo (-1 : ℝ) 1) ≃ₜ
        ((Subtype.val : R → X) ⁻¹' C),
      (∀ z, ((G z : R) : X) =
        (H (⟨((z.1 : R) : X), z.1.property⟩, z.2) : X)) ∧
      (∀ s, (G (bicollarBase s) : R) = (s : R)) ∧
      ∀ z, (G z : R) ∈ (Subtype.val : R → X) ⁻¹' K ↔
        0 ≤ (z.2 : ℝ) := by
  have hSR : S ⊆ R := by
    intro s hs
    have hmem := hCR (H (bicollarBase (⟨s, hs⟩ : S))).property
    simpa only [hbase] using hmem
  have hsrange : S ⊆ range (Subtype.val : R → X) := by
    simpa only [Subtype.range_coe] using hSR
  have hcrange : C ⊆ range (Subtype.val : R → X) := by
    simpa only [Subtype.range_coe] using hCR
  let T : ((Subtype.val : R → X) ⁻¹' S) ≃ₜ S :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsrange
  let J : ((Subtype.val : R → X) ⁻¹' C) ≃ₜ C :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hcrange
  have hJ (z : C) : ((J.symm z : R) : X) = (z : X) := by
    exact congrArg (Subtype.val : C → X) (J.apply_symm_apply z)
  let G := (T.prodCongr (Homeomorph.refl (Ioo (-1 : ℝ) 1))).trans
    (H.trans J.symm)
  have hG (z : ((Subtype.val : R → X) ⁻¹' S) × Ioo (-1 : ℝ) 1) :
      ((G z : R) : X) = (H (T z.1, z.2) : X) := hJ _
  refine ⟨G, hG, ?_, ?_⟩
  · intro s
    apply Subtype.ext
    exact (hG (bicollarBase s)).trans (hbase (T s))
  · intro z
    change ((G z : R) : X) ∈ K ↔ 0 ≤ (z.2 : ℝ)
    rw [hG]
    exact hside (T z.1, z.2)

end BrownCollar
