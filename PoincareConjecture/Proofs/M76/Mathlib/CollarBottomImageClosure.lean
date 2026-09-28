import PoincareConjecture.Proofs.M76.Mathlib.CollarBottomClosure

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

theorem collar_bottom_image_mem_closure
    {B T : Set E} {upper : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    {x : E} (hx : x ∈ B) (hpos : 0 < upper x)
    (H : E → F) (hH : Continuous H) {Q : Set F}
    (hside : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 = x → 0 < (p : E × ℝ).2 → H (C p) ∈ Q) :
    H x ∈ closure Q := by
  let I := Icc (0 : ℝ) (upper x)
  let V : Set I := {z | 0 < (z : ℝ)}
  let z₀ : I := ⟨0, le_rfl, hpos.le⟩
  let P : I → {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} :=
    fun z => ⟨(x, z), hx, z.property⟩
  let f : I → F := fun z => H (C (P z))
  have hP : Continuous P :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have hf : Continuous f :=
    hH.comp (continuous_subtype_val.comp (C.continuous.comp hP))
  have hV : (Subtype.val : I → ℝ) '' V = Ioc 0 (upper x) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw, w.property.2⟩
    · intro hz
      exact ⟨⟨z, hz.1.le, hz.2⟩, hz.1, rfl⟩
  have hz₀ : z₀ ∈ closure V := by
    rw [closure_subtype, hV, closure_Ioc hpos.ne]
    exact ⟨le_rfl, hpos.le⟩
  have hmap : MapsTo f V Q := fun z hz => hside (P z) rfl hz
  have hzero : f z₀ = H x := congrArg H (hbottom (P z₀) rfl)
  rw [← hzero]
  exact hf.continuousWithinAt.mem_closure hz₀ hmap

end Homeomorph
