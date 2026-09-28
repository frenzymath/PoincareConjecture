import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}




theorem OriginalDiskProduct.exists_thin_open_strips (P : OriginalDiskProduct e R j)
    {W : Set R} (hW : IsOpen W)
    (hcenter : ∀ z : D,
      (⟨P.map ((z : V2), 0), P.inside ⟨z.property, by norm_num⟩⟩ : R) ∈ W)
    (hWimage : (Subtype.val : R → X) '' W ⊆ P.map '' (D ×ˢ I)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      MapsTo P.map (D ×ˢ Icc (-δ) δ) ((Subtype.val : R → X) '' W) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) := by
  let f : D × I → R := fun z =>
    ⟨P.map ((z.1 : V2), (z.2 : ℝ)), P.inside ⟨z.1.property, z.2.property⟩⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact P.polyhedral.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨z.1.property, z.2.property⟩)
  have hemb : Topology.IsEmbedding f :=
    (P.embedding.isEmbedding.comp (Homeomorph.Set.prod D I).symm.isEmbedding).codRestrict
      R (fun z => P.inside ⟨z.1.property, z.2.property⟩)
  have hWrange : W ⊆ range f := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hWimage ⟨y, hy, rfl⟩
    exact ⟨(⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩), Subtype.ext hzy⟩
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V2) 1)
  obtain ⟨δ, hδ, hδsmall, hstrip⟩ := hf.exists_closed_strip_subset hW hcenter
  refine ⟨δ, hδ, hδsmall, ?_, ?_⟩
  · intro z hz
    have htI : z.2 ∈ I := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    exact ⟨f (⟨z.1, hz.1⟩, ⟨z.2, htI⟩),
      hstrip ⟨z.1, hz.1⟩ ⟨z.2, htI⟩ (abs_le.mpr hz.2), rfl⟩
  · intro ε hε hεδ
    let S : Set (D × I) := {z | (z.2 : ℝ) ∈ Ioo (-ε) ε}
    have hS : IsOpen S := isOpen_Ioo.preimage
      (continuous_subtype_val.comp continuous_snd)
    have hSW : f '' S ⊆ W := by
      rintro _ ⟨z, hz, rfl⟩
      apply hstrip z.1 z.2
      exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hopen := hemb.isInducing.isOpen_image_of_subset_open hS hW hSW hWrange
    have heq : f '' S = (Subtype.val : R → X) ⁻¹'
        (P.map '' (D ×ˢ Ioo (-ε) ε)) := by
      ext y
      constructor
      · rintro ⟨z, hz, hzy⟩
        exact ⟨((z.1 : V2), (z.2 : ℝ)), ⟨z.1.property, hz⟩,
          congrArg (Subtype.val : R → X) hzy⟩
      · rintro ⟨z, hz, hzy⟩
        have htI : z.2 ∈ I := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
        exact ⟨(⟨z.1, hz.1⟩, ⟨z.2, htI⟩), hz.2, Subtype.ext hzy⟩
    exact heq ▸ hopen

end PoincareConjecture.M76
