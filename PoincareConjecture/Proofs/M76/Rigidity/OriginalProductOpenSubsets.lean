import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}



theorem OriginalDiskProduct.isOpen_image_parameter_subset (P : OriginalDiskProduct e R j)
    (hopenP : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D ×ˢ Ioo (-1 : ℝ) 1)))) {A : Set E}
    (hA : A ⊆ D ×ˢ Ioo (-1 : ℝ) 1)
    (hopenA : IsOpen ((Subtype.val : (D ×ˢ I : Set E) → E) ⁻¹' A)) :
    IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' A)) := by
  let f : (D ×ˢ I : Set E) → R := fun z => ⟨P.map z, P.inside z.property⟩
  have hf : Topology.IsEmbedding f :=
    P.embedding.isEmbedding.codRestrict R (fun z => P.inside z.property)
  let W := (Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-1 : ℝ) 1))
  let V := (Subtype.val : (D ×ˢ I : Set E) → E) ⁻¹' A
  have hVW : f '' V ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨(z : E), hA hz, rfl⟩
  have hWrange : W ⊆ range f := by
    rintro y ⟨z, hz, hzy⟩
    exact ⟨⟨z, hz.1, Ioo_subset_Icc_self hz.2⟩, Subtype.ext hzy⟩
  have hopen := hf.isInducing.isOpen_image_of_subset_open hopenA hopenP hVW hWrange
  have heq : f '' V = (Subtype.val : R → X) ⁻¹' (P.map '' A) := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      exact ⟨(z : E), hz, congrArg (Subtype.val : R → X) hzy⟩
    · rintro ⟨z, hz, hzy⟩
      have hzin := hA hz
      exact ⟨⟨z, hzin.1, Ioo_subset_Icc_self hzin.2⟩, hz, Subtype.ext hzy⟩
  exact heq ▸ hopen

end PoincareConjecture.M76
