import Mathlib.Topology.OpenPartialHomeomorph.Composition









set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



theorem exists_extension_away_from_closed {T W C : Set X}
    (q : OpenPartialHomeomorph T Y) (hTW : T ⊆ W) (hcover : W ⊆ T ∪ C)
    (hC : IsClosed C) (p : T) (hp : p ∈ q.source) (hpC : (p : X) ∉ C) :
    ∃ e : OpenPartialHomeomorph W Y,
      e.source = (Subtype.val : W → X) ⁻¹'
        (((Subtype.val : T → X) '' q.source) \ C) ∧
      e.target = q.target ∩ {y | (q.symm y : X) ∉ C} ∧
      (⟨p, hTW p.property⟩ : W) ∈ e.source ∧
      (∀ x : T, e ⟨x, hTW x.property⟩ = q x) ∧
      ∀ y : Y, (e.symm y : X) = (q.symm y : X) := by
  classical
  let r : W → T := fun w => if hw : (w : X) ∈ T then ⟨w, hw⟩ else p
  have hr (w : W) (hw : (w : X) ∈ T) : (r w : X) = w := by
    dsimp only [r]
    rw [dif_pos hw]
  have houtside (w : W) (hw : (w : X) ∉ C) : (w : X) ∈ T :=
    (hcover w.property).resolve_right hw
  let j : OpenPartialHomeomorph W T := {
    toFun := r
    invFun := fun x => ⟨x, hTW x.property⟩
    source := (Subtype.val : W → X) ⁻¹' Cᶜ
    target := (Subtype.val : T → X) ⁻¹' Cᶜ
    map_source' := by
      intro w hw
      change (r w : X) ∉ C
      rw [hr w (houtside w hw)]
      exact hw
    map_target' := fun _ hx => hx
    left_inv' := by
      intro w hw
      exact Subtype.ext (hr w (houtside w hw))
    right_inv' := by
      intro x hx
      exact Subtype.ext (hr ⟨x, hTW x.property⟩ x.property)
    continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      (continuous_subtype_val.continuousOn.congr (fun w hw => hr w (houtside w hw)))
    continuousOn_invFun :=
      (continuous_subtype_val.subtype_mk (fun x => hTW x.property)).continuousOn
    open_source := hC.isOpen_compl.preimage continuous_subtype_val
    open_target := hC.isOpen_compl.preimage continuous_subtype_val }
  let e := j.trans q
  have heSource : e.source = (Subtype.val : W → X) ⁻¹'
      (((Subtype.val : T → X) '' q.source) \ C) := by
    rw [show e.source = j.source ∩ j ⁻¹' q.source from j.trans_source q]
    ext w
    constructor
    · rintro ⟨hw, hq⟩
      exact ⟨⟨r w, hq, hr w (houtside w hw)⟩, hw⟩
    · rintro ⟨⟨x, hx, hval⟩, hw⟩
      refine ⟨hw, ?_⟩
      have hrx : r w = x := Subtype.ext ((hr w (houtside w hw)).trans hval.symm)
      change r w ∈ q.source
      rwa [hrx]
  refine ⟨e, heSource, rfl, ?_, ?_, fun _ => rfl⟩
  · rw [heSource]
    exact ⟨⟨p, hp, rfl⟩, hpC⟩
  · intro x
    change q (r ⟨x, hTW x.property⟩) = q x
    exact congrArg q (Subtype.ext (hr ⟨x, hTW x.property⟩ x.property))



theorem exists_extension_to_finite_caps {ι : Type*} [Finite ι]
    (P : Set X) (D : ι → Set X) (hclosed : ∀ i, IsClosed (D i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) (i : ι)
    (q : OpenPartialHomeomorph (P ∪ D i : Set X) Y) (p : (P ∪ D i : Set X))
    (hp : p ∈ q.source) (hpD : (p : X) ∈ D i) :
    ∃ e : OpenPartialHomeomorph (P ∪ ⋃ j, D j : Set X) Y,
      e.source = (Subtype.val : (P ∪ ⋃ j, D j : Set X) → X) ⁻¹'
        (((Subtype.val : (P ∪ D i : Set X) → X) '' q.source) \ ⋃ j : {j // j ≠ i}, D j) ∧
      e.target = q.target ∩ {y | (q.symm y : X) ∉ ⋃ j : {j // j ≠ i}, D j} ∧
      (∀ x : (P ∪ D i : Set X), e ⟨x, Or.elim x.property Or.inl
        (fun hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩))⟩ = q x) ∧
      (∀ y : Y, (e.symm y : X) = (q.symm y : X)) ∧
      (⟨p, Or.elim p.property Or.inl
        (fun hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩))⟩ : (P ∪ ⋃ j, D j : Set X)) ∈ e.source := by
  classical
  let C := ⋃ j : {j // j ≠ i}, D j
  have hC : IsClosed C := isClosed_iUnion_of_finite (fun j => hclosed j)
  have hTW : P ∪ D i ⊆ P ∪ ⋃ j, D j := by
    intro x hx
    exact hx.elim Or.inl (fun h => Or.inr (mem_iUnion.mpr ⟨i, h⟩))
  have hcover : (P ∪ ⋃ j, D j) ⊆ (P ∪ D i) ∪ C := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · exact Or.inl (Or.inr (hji ▸ hj))
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hpC : (p : X) ∉ C := by
    intro hpC
    obtain ⟨j, hj⟩ := mem_iUnion.mp hpC
    exact disjoint_left.mp (hdis j.property.symm) hpD hj
  obtain ⟨e, hs, ht, hp', hf, hg⟩ :=
    q.exists_extension_away_from_closed hTW hcover hC p hp hpC
  exact ⟨e, hs, ht, hf, hg, hp'⟩

end OpenPartialHomeomorph
