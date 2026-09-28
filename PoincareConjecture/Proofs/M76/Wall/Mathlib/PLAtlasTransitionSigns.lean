import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLLocalSignComposition











set_option autoImplicit false

open Set

namespace Geometry

private theorem mem_original_atlas_transition
    {X E ι : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (e : ι → OpenPartialHomeomorph X E) (i j : ι) {x : X}
    (hi : x ∈ (e i).source) (hj : x ∈ (e j).source) :
    e i x ∈ ((e i).symm.trans (e j)).source := by
  refine ⟨(e i).map_source hi, ?_⟩
  change (e i).symm (e i x) ∈ (e j).source
  rw [(e i).left_inv hi]
  exact hj

variable {X E ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]




noncomputable def plAtlasTransitionSign
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (i j : ι) (x : ((e i).source ∩ (e j).source : Set X)) : SignType :=
  plLocalSign ((e i).symm.trans (e j)) (hcompat i j)
    ⟨e i x, mem_original_atlas_transition e i j x.property.1 x.property.2⟩



theorem plAtlasTransitionSign_ne_zero
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (i j : ι) (x : ((e i).source ∩ (e j).source : Set X)) :
    plAtlasTransitionSign e hcompat i j x ≠ 0 :=
  plLocalSign_ne_zero _ _ _



theorem isLocallyConstant_plAtlasTransitionSign
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (i j : ι) : IsLocallyConstant (plAtlasTransitionSign e hcompat i j) := by
  let h := (e i).symm.trans (e j)
  let q : ((e i).source ∩ (e j).source : Set X) → h.source := fun x =>
    ⟨e i x, mem_original_atlas_transition e i j x.property.1 x.property.2⟩
  have hc : Continuous (fun x : ((e i).source ∩ (e j).source : Set X) => e i x) :=
    (e i).continuousOn.comp_continuous continuous_subtype_val (fun x => x.property.1)
  have hq : Continuous q := hc.subtype_mk _
  exact (isLocallyConstant_plLocalSign h (hcompat i j)).comp_continuous hq



theorem plAtlasTransitionSign_self
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (i : ι) (x : (e i).source) :
    plAtlasTransitionSign e hcompat i i ⟨x, x.property, x.property⟩ = 1 := by
  let h := (e i).symm.trans (e i)
  have hs := mem_original_atlas_transition e i i x.property x.property
  have heq := plLocalSign_eq_of_eqOn h (OpenPartialHomeomorph.refl E)
    (hcompat i i) (piecewiseAffineGroupoid E).id_mem hs (mem_univ _)
    (e i).open_target ((e i).map_source x.property)
    (fun y hy => (e i).right_inv hy)
  exact heq.trans (plLocalSign_refl ⟨e i x, mem_univ _⟩)




theorem plAtlasTransitionSign_cocycle
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (i j k : ι) (x : X)
    (hi : x ∈ (e i).source) (hj : x ∈ (e j).source) (hk : x ∈ (e k).source) :
    plAtlasTransitionSign e hcompat j k ⟨x, hj, hk⟩ *
        plAtlasTransitionSign e hcompat i j ⟨x, hi, hj⟩ =
      plAtlasTransitionSign e hcompat i k ⟨x, hi, hk⟩ := by
  let hij := (e i).symm.trans (e j)
  let hjk := (e j).symm.trans (e k)
  let hik := (e i).symm.trans (e k)
  have hxij : e i x ∈ hij.source := mem_original_atlas_transition e i j hi hj
  have hxik : e i x ∈ hik.source := mem_original_atlas_transition e i k hi hk
  have hcoord : hij (e i x) = e j x := by
    change e j ((e i).symm (e i x)) = e j x
    rw [(e i).left_inv hi]
  have hxjk : hij (e i x) ∈ hjk.source := by
    rw [hcoord]
    exact mem_original_atlas_transition e j k hj hk
  let zi : hij.source := ⟨e i x, hxij⟩
  let zm : hjk.source := ⟨hij (e i x), hxjk⟩
  let zj : hjk.source := ⟨e j x, mem_original_atlas_transition e j k hj hk⟩
  let z : (hij.trans hjk).source := ⟨e i x, hxij, hxjk⟩
  have hmid : zm = zj := Subtype.ext hcoord
  let W := (e i).target ∩ (e i).symm ⁻¹' ((e j).source ∩ (e k).source)
  have hW : IsOpen W :=
    (e i).isOpen_inter_preimage_symm ((e j).open_source.inter (e k).open_source)
  have hxW : e i x ∈ W := by
    refine ⟨(e i).map_source hi, ?_⟩
    change (e i).symm (e i x) ∈ (e j).source ∩ (e k).source
    rw [(e i).left_inv hi]
    exact ⟨hj, hk⟩
  have hagree : EqOn (hij.trans hjk) hik W := by
    intro y hy
    change e k ((e j).symm (e j ((e i).symm y))) = e k ((e i).symm y)
    rw [(e j).left_inv hy.2.1]
  have hsame := plLocalSign_eq_of_eqOn (hij.trans hjk) hik
    ((piecewiseAffineGroupoid E).trans (hcompat i j) (hcompat j k))
    (hcompat i k) z.property hxik hW hxW hagree
  have hmul := plLocalSign_trans hij hjk (hcompat i j) (hcompat j k) z
  calc
    plAtlasTransitionSign e hcompat j k ⟨x, hj, hk⟩ *
        plAtlasTransitionSign e hcompat i j ⟨x, hi, hj⟩ =
      plLocalSign hjk (hcompat j k) zj * plLocalSign hij (hcompat i j) zi := rfl
    _ = plLocalSign hjk (hcompat j k) zm * plLocalSign hij (hcompat i j) zi := by
      rw [hmid]
    _ = plLocalSign (hij.trans hjk)
        ((piecewiseAffineGroupoid E).trans (hcompat i j) (hcompat j k)) z := hmul.symm
    _ = plAtlasTransitionSign e hcompat i k ⟨x, hi, hk⟩ := hsame



theorem plAtlasTransitionSign_symm
    (e : ι → OpenPartialHomeomorph X E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (i j : ι) (x : ((e i).source ∩ (e j).source : Set X)) :
    plAtlasTransitionSign e hcompat j i ⟨x, x.property.2, x.property.1⟩ =
      plAtlasTransitionSign e hcompat i j x := by
  have hp := plAtlasTransitionSign_cocycle e hcompat i j i x
    x.property.1 x.property.2 x.property.1
  rw [plAtlasTransitionSign_self e hcompat i ⟨x, x.property.1⟩] at hp
  cases ha : plAtlasTransitionSign e hcompat j i ⟨x, x.property.2, x.property.1⟩ <;>
    cases hb : plAtlasTransitionSign e hcompat i j x <;> simp_all

end Geometry
