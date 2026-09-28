import PoincareConjecture.Proofs.M76.Mathlib.CollarBottomClosure










set_option autoImplicit false

open Set

namespace Homeomorph

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]





theorem mem_height_closures_of_variableBand
    {B : Set E} {T : Set F} {lower upper : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} ≃ₜ T)
    (A : F → ℝ) (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}) :
    (lower (p : E × ℝ).1 < (p : E × ℝ).2 →
      (C p : F) ∈ closure (T ∩ {y | A y < A (C p)})) ∧
    ((p : E × ℝ).2 < upper (p : E × ℝ).1 →
      (C p : F) ∈ closure (T ∩ {y | A (C p) < A y})) := by
  let I := Icc (lower (p : E × ℝ).1) (upper (p : E × ℝ).1)
  let zc : I := ⟨(p : E × ℝ).2, p.property.2⟩
  let P : I → {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} :=
    fun z => ⟨((p : E × ℝ).1, z), p.property.1, z.property⟩
  let f : I → F := fun z => C (P z)
  have hP : Continuous P :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have hf : Continuous f := continuous_subtype_val.comp (C.continuous.comp hP)
  have hfc : f zc = (C p : F) := rfl
  constructor
  · intro hlo
    let V : Set I := {z | (z : ℝ) < (p : E × ℝ).2}
    have himage : (Subtype.val : I → ℝ) '' V =
        Ico (lower (p : E × ℝ).1) (p : E × ℝ).2 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.property.1, hw⟩
      · intro hz
        exact ⟨⟨z, hz.1, hz.2.le.trans p.property.2.2⟩, hz.2, rfl⟩
    have hz : zc ∈ closure V := by
      rw [closure_subtype, himage, closure_Ico hlo.ne]
      exact ⟨hlo.le, le_rfl⟩
    rw [← hfc]
    apply hf.continuousWithinAt.mem_closure hz
    intro z hz
    refine ⟨(C (P z)).property, ?_⟩
    change A (C (P z)) < A (C p)
    rw [hheight (P z), hheight p]
    exact hz
  · intro hhi
    let V : Set I := {z | (p : E × ℝ).2 < (z : ℝ)}
    have himage : (Subtype.val : I → ℝ) '' V =
        Ioc (p : E × ℝ).2 (upper (p : E × ℝ).1) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, w.property.2⟩
      · intro hz
        exact ⟨⟨z, p.property.2.1.trans hz.1.le, hz.2⟩, hz.1, rfl⟩
    have hz : zc ∈ closure V := by
      rw [closure_subtype, himage, closure_Ioc hhi.ne]
      exact ⟨le_rfl, hhi.le⟩
    rw [← hfc]
    apply hf.continuousWithinAt.mem_closure hz
    intro z hz
    refine ⟨(C (P z)).property, ?_⟩
    change A (C p) < A (C (P z))
    rw [hheight p, hheight (P z)]
    exact hz

end Homeomorph
