import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set unitInterval

namespace PoincareConjecture.M76

theorem exists_homotopy_in_disjoint_open_mark
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} (F : Bool → Set X) (hF : ∀ b, F b ⊆ A)
    (hopen : ∀ b, IsOpen ((Subtype.val : A → X) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (b : Bool) (f : C(Y, F b)) (H : C(I × Y, ↥(F false ∪ F true)))
    (hzero : ∀ y, (H (0, y) : X) = (f y : X)) :
    ∃ (g : C(Y, F b)) (eta : f.Homotopy g),
      ∀ s y, (eta (s, y) : X) = (H (s, y) : X) := by
  let inclusion : C(↥(F false ∪ F true), A) :=
    ContinuousMap.inclusion (union_subset (hF false) (hF true))
  have hopen' (c : Bool) : IsOpen
      ((Subtype.val : ↥(F false ∪ F true) → X) ⁻¹' F c) :=
    (hopen c).preimage inclusion.continuous
  have hcompl : ((Subtype.val : ↥(F false ∪ F true) → X) ⁻¹' F b)ᶜ =
      (Subtype.val : ↥(F false ∪ F true) → X) ⁻¹' F (!b) := by
    ext x
    change ((x : X) ∉ F b) ↔ (x : X) ∈ F (!b)
    cases b
    · exact ⟨fun hn ↦ x.property.resolve_left hn,
        fun hx hn ↦ disjoint_left.mp hdis hn hx⟩
    · exact ⟨fun hn ↦ x.property.resolve_right hn,
        fun hx hn ↦ disjoint_left.mp hdis hx hn⟩
  have hclopen : IsClopen ((Subtype.val : ↥(F false ∪ F true) → X) ⁻¹' F b) :=
    ⟨isOpen_compl_iff.mp (hcompl.symm ▸ hopen' (!b)), hopen' b⟩
  have hstay (s : I) (y : Y) : (H (s, y) : X) ∈ F b := by
    let trace : C(I, ↥(F false ∪ F true)) :=
      H.comp ⟨fun t ↦ (t, y), continuous_id.prodMk continuous_const⟩
    have hstart : trace 0 ∈ (Subtype.val : ↥(F false ∪ F true) → X) ⁻¹' F b := by
      change (H (0, y) : X) ∈ F b
      rw [hzero]
      exact (f y).property
    have hall := (hclopen.preimage trace.continuous).eq_univ ⟨0, hstart⟩
    exact (show s ∈ trace ⁻¹' ((Subtype.val : ↥(F false ∪ F true) → X) ⁻¹' F b) from
      hall.symm ▸ mem_univ s)
  let g : C(Y, F b) := ⟨fun y ↦ ⟨H (1, y), hstay 1 y⟩,
    (continuous_subtype_val.comp
      (H.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  refine ⟨g, {
    toFun := fun z ↦ ⟨H z, hstay z.1 z.2⟩
    continuous_toFun := (continuous_subtype_val.comp H.continuous).subtype_mk _
    map_zero_left := fun y ↦ Subtype.ext (hzero y)
    map_one_left := fun _ ↦ rfl }, fun _ _ ↦ rfl⟩

end PoincareConjecture.M76
