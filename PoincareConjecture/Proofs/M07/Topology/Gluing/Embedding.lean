import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas








set_option autoImplicit false
open Set Topology

namespace Poincare.Gluing



theorem exists_isOpenEmbedding_iUnion_ranges
    {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {Q Z : Type*} [TopologicalSpace Q] [TopologicalSpace Z]
    {q : ∀ i, X i → Q} (hq : ∀ i, IsOpenEmbedding (q i))
    {f : ∀ i, X i → Z} (hf : ∀ i, IsOpenEmbedding (f i))
    (hident : ∀ i j x y, f i x = f j y ↔ q i x = q j y) :
    ∃ F : (⋃ i, range (q i)) → Z, IsOpenEmbedding F ∧
      ∀ i x, F ⟨q i x, mem_iUnion.mpr ⟨i, mem_range_self x⟩⟩ = f i x := by
  classical
  let V := ⋃ i, range (q i)
  have hV : IsOpen V := isOpen_iUnion (fun i => (hq i).isOpen_range)
  have hrep (x : V) : ∃ i y, q i y = x := by
    simpa only [V, mem_iUnion, mem_range] using x.property
  choose a b hab using hrep
  let F : V → Z := fun x => f (a x) (b x)
  let qi (i : ι) : X i → V := fun x => ⟨q i x, mem_iUnion.mpr ⟨i, mem_range_self x⟩⟩
  have hqi (i : ι) : IsOpenEmbedding (qi i) :=
    hV.isOpenEmbedding_subtypeVal.of_comp (qi i) (hq i)
  have hFq (i : ι) (x : X i) : F (qi i x) = f i x :=
    (hident (a (qi i x)) i (b (qi i x)) x).mpr (hab (qi i x))
  have hcover (x : V) : qi (a x) (b x) = x := Subtype.ext (hab x)
  refine ⟨F, IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_, hFq⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    rw [← hcover x]
    apply (hqi (a x)).continuousAt_iff.mp
    simpa only [show F ∘ qi (a x) = f (a x) from funext (hFq (a x))] using
      (hf (a x)).continuous.continuousAt (x := b x)
  · intro x y hxy
    apply Subtype.ext
    exact (hab x).symm.trans (((hident (a x) (a y) (b x) (b y)).mp hxy).trans (hab y))
  · intro W hW
    have himage : F '' W = ⋃ i, f i '' ((qi i) ⁻¹' W) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact mem_iUnion.mpr ⟨a x, b x, by simpa only [mem_preimage, hcover] using hx,
          (hFq (a x) (b x)).symm.trans (congrArg F (hcover x))⟩
      · intro hz
        obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hz
        exact ⟨qi i x, hx, hFq i x⟩
    rw [himage]
    exact isOpen_iUnion (fun i => (hf i).isOpenMap _ (hW.preimage (hqi i).continuous))

theorem exists_isOpenEmbedding_union
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    {f : U → Y} {g : V → Y}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hident : ∀ x y, f x = g y ↔ (x : X) = y) :
    ∃ F : (U ∪ V : Set X) → Y, IsOpenEmbedding F ∧
      (∀ x : U, F ⟨x, Or.inl x.property⟩ = f x) ∧
      (∀ y : V, F ⟨y, Or.inr y.property⟩ = g y) := by
  classical
  let F : (U ∪ V : Set X) → Y := fun x =>
    if h : (x : X) ∈ U then f ⟨x, h⟩ else g ⟨x, x.property.resolve_left h⟩
  have hleft (x : U) : F ⟨x, Or.inl x.property⟩ = f x := by
    simp only [F, dif_pos x.property]
  have hright (y : V) : F ⟨y, Or.inr y.property⟩ = g y := by
    by_cases hy : (y : X) ∈ U
    · exact (dif_pos hy).trans ((hident ⟨y, hy⟩ y).mpr rfl)
    · exact dif_neg hy
  let u : U → (U ∪ V : Set X) := inclusion subset_union_left
  let v : V → (U ∪ V : Set X) := inclusion subset_union_right
  have hu : IsOpenEmbedding u := .inclusion _ (hU.preimage continuous_subtype_val)
  have hv : IsOpenEmbedding v := .inclusion _ (hV.preimage continuous_subtype_val)
  have hFu : F ∘ u = f := funext hleft
  have hFv : F ∘ v = g := funext hright
  refine ⟨F, IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_, hleft, hright⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    rcases x.property with hx | hx
    · apply (hu.continuousAt_iff (x := (⟨x, hx⟩ : U))).mp
      rw [hFu]
      exact hf.continuous.continuousAt
    · apply (hv.continuousAt_iff (x := (⟨x, hx⟩ : V))).mp
      rw [hFv]
      exact hg.continuous.continuousAt
  · intro x y hxy
    apply Subtype.ext
    rcases x.property with hx | hx <;> rcases y.property with hy | hy
    · have hfx : F x = f ⟨x, hx⟩ := hleft ⟨x, hx⟩
      have hfy : F y = f ⟨y, hy⟩ := hleft ⟨y, hy⟩
      exact congrArg (fun z : U => (z : X)) (hf.injective (hfx.symm.trans (hxy.trans hfy)))
    · exact (hident ⟨x, hx⟩ ⟨y, hy⟩).mp
        ((hleft ⟨x, hx⟩).symm.trans (hxy.trans (hright ⟨y, hy⟩)))
    · exact ((hident ⟨y, hy⟩ ⟨x, hx⟩).mp
        ((hleft ⟨y, hy⟩).symm.trans (hxy.symm.trans (hright ⟨x, hx⟩)))).symm
    · exact congrArg (fun z : V => (z : X)) (hg.injective
        ((hright ⟨x, hx⟩).symm.trans (hxy.trans (hright ⟨y, hy⟩))))
  · intro W hW
    have himage : F '' W = f '' (u ⁻¹' W) ∪ g '' (v ⁻¹' W) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases x.property with hxu | hxv
        · exact Or.inl ⟨⟨x, hxu⟩, hx, (hleft ⟨x, hxu⟩).symm⟩
        · exact Or.inr ⟨⟨x, hxv⟩, hx, (hright ⟨x, hxv⟩).symm⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨u x, hx, hleft x⟩
        · exact ⟨v x, hx, hright x⟩
    rw [himage]
    exact (hf.isOpenMap _ (hW.preimage hu.continuous)).union
      (hg.isOpenMap _ (hW.preimage hv.continuous))

theorem exists_isOpenEmbedding_union_ranges
    {X Y Q Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Q] [TopologicalSpace Z]
    {i : X → Q} {j : Y → Q} (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)
    {f : X → Z} {g : Y → Z} (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hident : ∀ x y, f x = g y ↔ i x = j y) :
    ∃ F : (range i ∪ range j : Set Q) → Z, IsOpenEmbedding F ∧
      (∀ x, F ⟨i x, Or.inl (mem_range_self x)⟩ = f x) ∧
      (∀ y, F ⟨j y, Or.inr (mem_range_self y)⟩ = g y) := by
  let a := hi.isEmbedding.toHomeomorph
  let b := hj.isEmbedding.toHomeomorph
  have ha (x : range i) : i (a.symm x) = x :=
    congrArg Subtype.val (a.apply_symm_apply x)
  have hb (y : range j) : j (b.symm y) = y :=
    congrArg Subtype.val (b.apply_symm_apply y)
  obtain ⟨F, hF, hleft, hright⟩ := exists_isOpenEmbedding_union hi.isOpen_range hj.isOpen_range
    (hf.comp a.symm.isOpenEmbedding) (hg.comp b.symm.isOpenEmbedding) (fun x y => by
      simpa only [Function.comp_apply, ha, hb] using hident (a.symm x) (b.symm y))
  refine ⟨F, hF, ?_, ?_⟩
  · intro x
    simpa only [Function.comp_apply, a, IsEmbedding.toHomeomorph_symm_apply] using
      hleft ⟨i x, mem_range_self x⟩
  · intro y
    simpa only [Function.comp_apply, b, IsEmbedding.toHomeomorph_symm_apply] using
      hright ⟨j y, mem_range_self y⟩

end Poincare.Gluing
