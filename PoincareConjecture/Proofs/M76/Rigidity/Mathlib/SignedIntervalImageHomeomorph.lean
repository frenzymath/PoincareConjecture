import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Topology.IsEmbedding

theorem exists_signed_interval_image_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {rho : ℝ} {c : ℝ → X} {d : ℝ → Y}
    (hc : IsEmbedding (fun t : Icc (-rho) rho => c t))
    (hd : IsEmbedding (fun t : Icc (-rho) rho => d t))
    (reverse : Bool) {g : X → Y}
    (hvalue : ∀ t ∈ Icc (-rho) rho, g (c t) = d (if reverse then -t else t)) :
    ∃ H : (c '' Icc (-rho) rho) ≃ₜ (d '' Icc (-rho) rho),
      ∀ y : (c '' Icc (-rho) rho), (H y : Y) = g y := by
  let B : Set ℝ := Icc (-rho) rho
  have hneg (t : ℝ) : t ∈ B ↔ -t ∈ B := by
    change (-rho ≤ t ∧ t ≤ rho) ↔ (-rho ≤ -t ∧ -t ≤ rho)
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
  let reflection : B ≃ₜ B := (Homeomorph.neg ℝ).subtype hneg
  let s : B ≃ₜ B := if reverse then reflection else Homeomorph.refl B
  have hs (t : B) : (s t : ℝ) = if reverse then -(t : ℝ) else (t : ℝ) := by
    cases reverse <;> rfl
  have hcrange : range (fun t : B => c t) = c '' B := by
    change range (c ∘ (Subtype.val : B → ℝ)) = c '' B
    rw [Set.range_comp, Subtype.range_val]
  have hdrange : range (fun t : B => d t) = d '' B := by
    change range (d ∘ (Subtype.val : B → ℝ)) = d '' B
    rw [Set.range_comp, Subtype.range_val]
  let Hc : B ≃ₜ (c '' B) := hc.toHomeomorph.trans (Homeomorph.setCongr hcrange)
  let Hd : B ≃ₜ (d '' B) := hd.toHomeomorph.trans (Homeomorph.setCongr hdrange)
  have hcv (t : B) : (Hc t : X) = c t := rfl
  have hdv (t : B) : (Hd t : Y) = d t := rfl
  let H : (c '' B) ≃ₜ (d '' B) := Hc.symm.trans (s.trans Hd)
  refine ⟨H, ?_⟩
  intro y
  let t : B := Hc.symm y
  have hty : Hc t = y := Hc.apply_symm_apply y
  have hct : c t = (y : X) :=
    (hcv t).symm.trans (congrArg (Subtype.val : c '' B → X) hty)
  change (Hd (s t) : Y) = g y
  rw [hdv, hs]
  exact (hvalue t t.property).symm.trans (congrArg g hct)

end Topology.IsEmbedding
