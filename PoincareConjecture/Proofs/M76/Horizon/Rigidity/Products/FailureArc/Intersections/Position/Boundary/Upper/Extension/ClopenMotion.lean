import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousOn

namespace PoincareConjecture.M76.UpperExtension

open Set

variable {X P : Type*}


noncomputable def extendSubsetMap (S : Set X) (f : S → S) (x : X) : X := by
  classical
  exact if hx : x ∈ S then f ⟨x, hx⟩ else x

@[simp] theorem extendSubsetMap_mem {S : Set X} (f : S → S) {x : X} (hx : x ∈ S) :
    extendSubsetMap S f x = f ⟨x, hx⟩ := by
  simp [extendSubsetMap, hx]

@[simp] theorem extendSubsetMap_not_mem {S : Set X} (f : S → S) {x : X}
    (hx : x ∉ S) : extendSubsetMap S f x = x := by
  simp [extendSubsetMap, hx]

variable [TopologicalSpace X] [TopologicalSpace P]


theorem continuous_extendSubsetMap {S : Set X} (hS : IsClopen S)
    (f : P → S → S) (hf : Continuous fun z : P × S => f z.1 z.2) :
    Continuous fun z : P × X => extendSubsetMap S (f z.1) z.2 := by
  let A : Set (P × X) := Prod.snd ⁻¹' S
  have hA : IsOpen A := hS.2.preimage continuous_snd
  have hAc : IsOpen Aᶜ := hS.1.isOpen_compl.preimage continuous_snd
  have hOn : ContinuousOn (fun z : P × X => extendSubsetMap S (f z.1) z.2) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous fun z : A => (z.val.1, (⟨z.val.2, z.property⟩ : S)) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    apply (continuous_subtype_val.comp (hf.comp hc)).congr
    intro z
    exact (extendSubsetMap_mem (f z.val.1) (show z.val.2 ∈ S from z.property)).symm
  have hOff : ContinuousOn (fun z : P × X => extendSubsetMap S (f z.1) z.2) Aᶜ := by
    apply continuous_snd.continuousOn.congr
    intro z hz
    exact extendSubsetMap_not_mem _ hz
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ A
  · exact hOn.continuousAt (hA.mem_nhds hz)
  · exact hOff.continuousAt (hAc.mem_nhds hz)


noncomputable def extendClopenHomeomorph {S : Set X} (hS : IsClopen S)
    (g : S ≃ₜ S) : X ≃ₜ X where
  toFun := extendSubsetMap S g
  invFun := extendSubsetMap S g.symm
  left_inv x := by
    by_cases hx : x ∈ S
    · simp only [extendSubsetMap_mem _ hx, extendSubsetMap_mem _ (g ⟨x, hx⟩).property]
      exact congrArg Subtype.val (g.symm_apply_apply ⟨x, hx⟩)
    · simp [extendSubsetMap_not_mem _ hx]
  right_inv x := by
    by_cases hx : x ∈ S
    · simp only [extendSubsetMap_mem _ hx,
        extendSubsetMap_mem _ (g.symm ⟨x, hx⟩).property]
      exact congrArg Subtype.val (g.apply_symm_apply ⟨x, hx⟩)
    · simp [extendSubsetMap_not_mem _ hx]
  continuous_toFun := by
    have hc := continuous_extendSubsetMap (P := Unit) hS (fun _ => g)
      (g.continuous.comp continuous_snd)
    exact hc.comp ((continuous_const (y := ())).prodMk continuous_id)
  continuous_invFun := by
    have hc := continuous_extendSubsetMap (P := Unit) hS (fun _ => g.symm)
      (g.symm.continuous.comp continuous_snd)
    exact hc.comp ((continuous_const (y := ())).prodMk continuous_id)


theorem exists_clopen_motion_extension {S : Set X} (hS : IsClopen S)
    (G : P → S ≃ₜ S)
    (hG : Continuous fun z : P × S => G z.1 z.2)
    (hGi : Continuous fun z : P × S => (G z.1).symm z.2)
    (t₀ : P) (hzero : G t₀ = Homeomorph.refl S) :
    ∃ H : P → X ≃ₜ X,
      Continuous (fun z : P × X => H z.1 z.2) ∧
      Continuous (fun z : P × X => (H z.1).symm z.2) ∧
      H t₀ = Homeomorph.refl X ∧
      (∀ t (x : S), H t x = G t x) ∧
      (∀ t x, x ∉ S → H t x = x) := by
  refine ⟨fun t => extendClopenHomeomorph hS (G t),
    continuous_extendSubsetMap hS (fun t => G t) hG,
    continuous_extendSubsetMap hS (fun t => (G t).symm) hGi, ?_, ?_, ?_⟩
  · ext x
    change extendSubsetMap S (G t₀) x = x
    rw [hzero]
    by_cases hx : x ∈ S <;> simp [extendSubsetMap, hx]
  · intro t x
    exact extendSubsetMap_mem _ x.property
  · intro t x hx
    exact extendSubsetMap_not_mem _ hx

end PoincareConjecture.M76.UpperExtension
