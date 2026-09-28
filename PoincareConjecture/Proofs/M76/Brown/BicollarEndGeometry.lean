import PoincareConjecture.Proofs.M76.Brown.OrientedBicollar
import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false

open Set

namespace BrownSchoenflies

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]

noncomputable def closedBicollarCoordinates (z : B × Icc (-1 : ℝ) 1) : B × Ioo (-1 : ℝ) 1 :=
  (z.1, ⟨(z.2 : ℝ) / 2, by
    constructor <;> linarith [z.2.property.1, z.2.property.2]⟩)

theorem continuous_closedBicollarCoordinates : Continuous (closedBicollarCoordinates (B := B)) := by
  unfold closedBicollarCoordinates
  fun_prop

noncomputable def closedBicollarMap (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X)
    (hes : e.source = univ) : C(B × Icc (-1 : ℝ) 1, X) :=
  ⟨e ∘ closedBicollarCoordinates,
    (e.isOpenEmbedding hes).continuous.comp continuous_closedBicollarCoordinates⟩

def bicollarBaseImage (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X) : Set X :=
  range (fun b => e (BrownCollar.bicollarBase b))

def middleBicollarBand (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X) : Set X :=
  e '' {z | -(1 / 2 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1 / 2}

theorem closedBicollarMap_injective (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X)
    (hes : e.source = univ) : Function.Injective (closedBicollarMap e hes) := by
  intro z w h
  have he := (e.isOpenEmbedding hes).isEmbedding.injective h
  refine Prod.ext (congrArg (fun v : B × Ioo (-1 : ℝ) 1 => v.1) he) (Subtype.ext ?_)
  have ht := congrArg (fun v : B × Ioo (-1 : ℝ) 1 => (v.2 : ℝ)) he
  change (z.2 : ℝ) / 2 = (w.2 : ℝ) / 2 at ht
  linarith

theorem isOpen_middleBicollarBand (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X)
    (hes : e.source = univ) : IsOpen (middleBicollarBand e) := by
  apply (e.isOpenEmbedding hes).isOpenMap
  have ht : Continuous (fun z : B × Ioo (-1 : ℝ) 1 => (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact (isOpen_lt continuous_const ht).inter (isOpen_lt ht continuous_const)

theorem bicollarBaseImage_subset_middle (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X) :
    bicollarBaseImage e ⊆ middleBicollarBand e := by
  rintro x ⟨b, rfl⟩
  exact ⟨BrownCollar.bicollarBase b, by constructor <;> norm_num [BrownCollar.bicollarBase], rfl⟩

theorem bicollar_apply_mem_baseImage_iff
    (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X) (hes : e.source = univ)
    (z : B × Ioo (-1 : ℝ) 1) : e z ∈ bicollarBaseImage e ↔ (z.2 : ℝ) = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    have he := (e.isOpenEmbedding hes).isEmbedding.injective hb
    exact (congrArg (fun v : B × Ioo (-1 : ℝ) 1 => (v.2 : ℝ)) he).symm
  · intro hz
    exact ⟨z.1, congrArg e (Prod.ext rfl (Subtype.ext hz.symm))⟩

theorem closedBicollarMap_mem_middle_iff
    (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X) (hes : e.source = univ)
    (z : B × Icc (-1 : ℝ) 1) :
    closedBicollarMap e hes z ∈ middleBicollarBand e ↔ -1 < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1 := by
  constructor
  · rintro ⟨w, hw, he⟩
    have hwz := (e.isOpenEmbedding hes).isEmbedding.injective he
    have ht := congrArg (fun v : B × Ioo (-1 : ℝ) 1 => (v.2 : ℝ)) hwz
    change (w.2 : ℝ) = (z.2 : ℝ) / 2 at ht
    constructor <;> linarith [hw.1, hw.2]
  · intro hz
    refine ⟨closedBicollarCoordinates z, ?_, rfl⟩
    change -(1 / 2 : ℝ) < (z.2 : ℝ) / 2 ∧ (z.2 : ℝ) / 2 < 1 / 2
    constructor <;> linarith [hz.1, hz.2]

theorem middleBicollarBand_subset_closed_range
    (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X) (hes : e.source = univ) :
    middleBicollarBand e ⊆ range (closedBicollarMap e hes) := by
  rintro x ⟨z, hz, rfl⟩
  let w : B × Icc (-1 : ℝ) 1 := (z.1, ⟨2 * (z.2 : ℝ), by
    constructor <;> linarith [hz.1, hz.2]⟩)
  refine ⟨w, congrArg e (Prod.ext rfl (Subtype.ext ?_))⟩
  change 2 * (z.2 : ℝ) / 2 = (z.2 : ℝ)
  ring

variable [Nonempty B]

theorem exists_closed_bicollar_ends
    (e : OpenPartialHomeomorph (B × Ioo (-1 : ℝ) 1) X) (hes : e.source = univ)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hunion : U ∪ V = (bicollarBaseImage e)ᶜ)
    (hneg : ∀ z, (z.2 : ℝ) < 0 → e z ∈ U)
    (hpos : ∀ z, 0 < (z.2 : ℝ) → e z ∈ V) :
    ∃ A D : Set X, IsClosed A ∧ IsClosed D ∧ Disjoint A D ∧
      A ⊆ U ∧ D ⊆ V ∧ A.Nonempty ∧ D.Nonempty ∧
      A ∪ range (closedBicollarMap e hes) ∪ D = univ ∧
      (∀ z, closedBicollarMap e hes z ∈ A ↔ (z.2 : ℝ) = -1) ∧
      (∀ z, closedBicollarMap e hes z ∈ D ↔ (z.2 : ℝ) = 1) := by
  classical
  let A := Vᶜ \ middleBicollarBand e
  let D := Uᶜ \ middleBicollarBand e
  have hM := isOpen_middleBicollarBand e hes
  have hAS : A ⊆ U := by
    intro x hx
    have hxP : x ∉ bicollarBaseImage e := fun h => hx.2 (bicollarBaseImage_subset_middle e h)
    exact ((hunion.symm.subset hxP)).resolve_right hx.1
  have hDS : D ⊆ V := by
    intro x hx
    have hxP : x ∉ bicollarBaseImage e := fun h => hx.2 (bicollarBaseImage_subset_middle e h)
    exact ((hunion.symm.subset hxP)).resolve_left hx.1
  have hVheight (z : B × Ioo (-1 : ℝ) 1) : e z ∈ V ↔ 0 < (z.2 : ℝ) := by
    constructor
    · intro hz
      by_contra hn
      have hle : (z.2 : ℝ) ≤ 0 := le_of_not_gt hn
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Set.disjoint_left.mp hUV (hneg z hlt) hz
      · exact (hunion.subset (Or.inr hz)) ((bicollar_apply_mem_baseImage_iff e hes z).mpr heq)
    · exact hpos z
  have hUheight (z : B × Ioo (-1 : ℝ) 1) : e z ∈ U ↔ (z.2 : ℝ) < 0 := by
    constructor
    · intro hz
      by_contra hn
      have hle : 0 ≤ (z.2 : ℝ) := le_of_not_gt hn
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Set.disjoint_left.mp hUV hz (hpos z hlt)
      · exact (hunion.subset (Or.inl hz)) ((bicollar_apply_mem_baseImage_iff e hes z).mpr heq.symm)
    · exact hneg z
  have hAend (z : B × Icc (-1 : ℝ) 1) :
      closedBicollarMap e hes z ∈ A ↔ (z.2 : ℝ) = -1 := by
    change (closedBicollarMap e hes z ∉ V ∧
      closedBicollarMap e hes z ∉ middleBicollarBand e) ↔ _
    rw [closedBicollarMap_mem_middle_iff]
    change (¬ e (closedBicollarCoordinates z) ∈ V) ∧ _ ↔ _
    rw [hVheight]
    change (¬ 0 < (z.2 : ℝ) / 2) ∧ ¬ (-1 < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1) ↔ _
    constructor
    · rintro ⟨hnpos, hnmid⟩
      have ht : (z.2 : ℝ) ≤ 0 := by linarith [le_of_not_gt hnpos]
      have hnlow : ¬ -1 < (z.2 : ℝ) := fun h => hnmid ⟨h, by linarith⟩
      exact le_antisymm (le_of_not_gt hnlow) z.2.property.1
    · intro hz
      rw [hz]
      norm_num
  have hDend (z : B × Icc (-1 : ℝ) 1) :
      closedBicollarMap e hes z ∈ D ↔ (z.2 : ℝ) = 1 := by
    change (closedBicollarMap e hes z ∉ U ∧
      closedBicollarMap e hes z ∉ middleBicollarBand e) ↔ _
    rw [closedBicollarMap_mem_middle_iff]
    change (¬ e (closedBicollarCoordinates z) ∈ U) ∧ _ ↔ _
    rw [hUheight]
    change (¬ (z.2 : ℝ) / 2 < 0) ∧ ¬ (-1 < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1) ↔ _
    constructor
    · rintro ⟨hnneg, hnmid⟩
      have ht : 0 ≤ (z.2 : ℝ) := by linarith [le_of_not_gt hnneg]
      have hnup : ¬ (z.2 : ℝ) < 1 := fun h => hnmid ⟨by linarith, h⟩
      exact le_antisymm z.2.property.2 (le_of_not_gt hnup)
    · intro hz
      rw [hz]
      norm_num
  let b : B := Classical.choice inferInstance
  refine ⟨A, D, hV.isClosed_compl.sdiff hM, hU.isClosed_compl.sdiff hM,
    hUV.mono hAS hDS, hAS, hDS, ?_, ?_, ?_, hAend, hDend⟩
  · exact ⟨closedBicollarMap e hes (b, ⟨-1, by constructor <;> norm_num⟩),
      (hAend _).mpr rfl⟩
  · exact ⟨closedBicollarMap e hes (b, ⟨1, by constructor <;> norm_num⟩),
      (hDend _).mpr rfl⟩
  · apply eq_univ_of_forall
    intro x
    by_cases hxM : x ∈ middleBicollarBand e
    · exact Or.inl (Or.inr (middleBicollarBand_subset_closed_range e hes hxM))
    · by_cases hxU : x ∈ U
      · exact Or.inl (Or.inl ⟨fun hxV => Set.disjoint_left.mp hUV hxU hxV, hxM⟩)
      · exact Or.inr ⟨hxU, hxM⟩

end BrownSchoenflies
