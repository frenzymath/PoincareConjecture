import PoincareConjecture.Proofs.M76.Rigidity.MeridianCutFrontierMap








set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {j : V2 → X}



theorem image_meridianCutFrontierMap (P : OriginalDiskProduct e R j)
    {a : ℝ} (hgap : a / 2 < p - a / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) :
    P.meridianCutFrontierMap a '' cubePrismBoundary (a / 2) (p - a / 2) =
      (hamiltonMeridianCutAmbientMap '' (Q ×ˢ Icc (a / 2) (p - a / 2))) ∪
        P.endDisks := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with hlat | hcap
    · exact Or.inl ⟨z, hlat, (P.meridianCutFrontierMap_lateral hgap hmark z hlat.1).symm⟩
    · have ht : z.2 = a / 2 ∨ z.2 = p - a / 2 := hcap.2
      apply Or.inr
      rcases ht with ht | ht
      · have hz' : z = (z.1, a / 2) := Prod.ext rfl ht
        refine ⟨(z.1, (1 / 2 : ℝ)), ⟨hcap.1, by simp⟩, ?_⟩
        rw [hz', P.meridianCutFrontierMap_lower]
      · have hz' : z = (z.1, p - a / 2) := Prod.ext rfl ht
        refine ⟨(z.1, -(1 / 2 : ℝ)), ⟨hcap.1, by simp⟩, ?_⟩
        rw [hz', P.meridianCutFrontierMap_upper hgap]
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, Or.inl hz, P.meridianCutFrontierMap_lateral hgap hmark z hz.1⟩
    · have ht : z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := hz.2
      rcases ht with ht | ht
      · refine ⟨(z.1, p - a / 2), Or.inr ⟨hz.1, by simp⟩, ?_⟩
        rw [P.meridianCutFrontierMap_upper hgap]
        exact congrArg P.map (Prod.ext rfl ht.symm)
      · refine ⟨(z.1, a / 2), Or.inr ⟨hz.1, by simp⟩, ?_⟩
        rw [P.meridianCutFrontierMap_lower]
        exact congrArg P.map (Prod.ext rfl ht.symm)



theorem image_meridianCutFrontierMap_eq_frontier (P : OriginalDiskProduct e R j)
    (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {a : ℝ} (ha : 0 < a) (hasmall : a ≤ 1 / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) :
    P.meridianCutFrontierMap a '' cubePrismBoundary (a / 2) (p - a / 2) =
      frontier P.cutCarrier := by
  let : T2Space T := hamiltonSolidTorusCircleEquiv.isEmbedding.t2Space
  have hgap : a / 2 < p - a / 2 := by norm_num at hasmall ⊢; linarith
  rw [P.image_meridianCutFrontierMap hgap hmark,
    P.marked_meridian_retained_frontier ha hasmall hmark,
    (P.cut_geometry hR hopen).2.2.1]

end PoincareConjecture.M76.OriginalDiskProduct
