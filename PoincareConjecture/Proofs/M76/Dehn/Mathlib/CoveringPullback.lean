import Mathlib.Topology.Covering.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

namespace CoveringPullback

variable {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace Y]

abbrev Total (p : E → X) (f : Y → X) := {z : Y × E // f z.1 = p z.2}

def proj (p : E → X) (f : Y → X) : Total p f → Y := fun z => z.1.1

omit [TopologicalSpace X] in

theorem continuous_proj (p : E → X) (f : Y → X) : Continuous (proj p f) :=
  continuous_fst.comp continuous_subtype_val

def fiberHomeomorph (p : E → X) (f : Y → X) (y : Y) :
    (proj p f ⁻¹' {y}) ≃ₜ (p ⁻¹' {f y}) where
  toFun z := ⟨z.1.1.2, z.1.2.symm.trans (congrArg f z.2)⟩
  invFun e := ⟨⟨(y, e.1), e.2.symm⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext z.2.symm rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _

omit [TopologicalSpace X] in

theorem fiber_ncard (p : E → X) (f : Y → X) (y : Y) :
    (proj p f ⁻¹' {y}).ncard = (p ⁻¹' {f y}).ncard :=
  ncard_congr' (fiberHomeomorph p f y).toEquiv

theorem isCoveringMap {p : E → X} (hp : IsCoveringMap p)
    {f : Y → X} (hf : Continuous f) : IsCoveringMap (proj p f) := by
  intro y
  obtain ⟨hdisc, U, hyU, hU, _, H, hH⟩ := hp (f y)
  let : DiscreteTopology (p ⁻¹' {f y}) := hdisc
  let V : Set Y := f ⁻¹' U
  let L : (proj p f ⁻¹' V) → (p ⁻¹' U) := fun z =>
    ⟨z.1.1.2, by
      change p z.1.1.2 ∈ U
      rw [← z.1.2]
      exact z.2⟩
  have hL : Continuous L :=
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  let T : (proj p f ⁻¹' V) ≃ₜ V × (p ⁻¹' {f y}) :=
    { toFun := fun z => (⟨proj p f z, z.2⟩, (H (L z)).2)
      invFun := fun z =>
        ⟨⟨(z.1.1, (H.symm (⟨f z.1, z.1.2⟩, z.2) : E)), by
          have hh := hH (H.symm (⟨f z.1, z.1.2⟩, z.2))
          simpa only [H.apply_symm_apply] using hh⟩, z.1.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hbase : (⟨f (proj p f z), z.2⟩ : U) = (H (L z)).1 := by
            apply Subtype.ext
            exact z.1.2.trans (hH (L z)).symm
          change (H.symm (⟨f (proj p f z), z.2⟩, (H (L z)).2) : E) = z.1.1.2
          rw [hbase]
          exact congrArg Subtype.val (H.symm_apply_apply (L z))
      right_inv := by
        intro z
        apply Prod.ext
        · rfl
        · change (H (H.symm (⟨f z.1, z.1.2⟩, z.2))).2 = z.2
          rw [H.apply_symm_apply]
      continuous_toFun :=
        ((continuous_proj p f).comp continuous_subtype_val).subtype_mk _ |>.prodMk
          (continuous_snd.comp (H.continuous.comp hL))
      continuous_invFun := by
        fun_prop }
  have hV : IsOpen V := hU.preimage hf
  have heven : IsEvenlyCovered (proj p f) y (p ⁻¹' {f y}) :=
    ⟨hdisc, V, hyU, hV, hV.preimage (continuous_proj p f), T, fun _ => rfl⟩
  exact heven.to_isEvenlyCovered_preimage

end CoveringPullback
