import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.List.Nodup









set_option autoImplicit false

open Set

namespace Geometry

variable {X T α : Type*} [TopologicalSpace X] [TopologicalSpace T]

theorem supported_homeomorph_mapsTo (H : X ≃ₜ X) {S : Set X}
    (hfix : EqOn H id Sᶜ) : MapsTo H S S := by
  intro x hx
  by_contra h
  have heq : H x = x := H.injective (hfix h)
  exact h (heq.symm ▸ hx)

def composeSupportedMotions (F : α → T → X ≃ₜ X) : List α → T → X ≃ₜ X
  | [], _ => Homeomorph.refl X
  | a :: l, t => (composeSupportedMotions F l t).trans (F a t)

theorem composeSupportedMotions_continuous
    (F : α → T → X ≃ₜ X)
    (hF : ∀ a, Continuous (fun z : T × X => F a z.1 z.2)) (l : List α) :
    Continuous (fun z : T × X => composeSupportedMotions F l z.1 z.2) := by
  induction l with
  | nil => exact continuous_snd
  | cons a l ih =>
    exact (hF a).comp (continuous_fst.prodMk ih)

theorem composeSupportedMotions_inverse_continuous
    (F : α → T → X ≃ₜ X)
    (hF : ∀ a, Continuous (fun z : T × X => (F a z.1).symm z.2)) (l : List α) :
    Continuous (fun z : T × X => (composeSupportedMotions F l z.1).symm z.2) := by
  induction l with
  | nil => exact continuous_snd
  | cons a l ih =>
    exact ih.comp (continuous_fst.prodMk (hF a))

omit [TopologicalSpace T] in
theorem composeSupportedMotions_initial
    (F : α → T → X ≃ₜ X) (t₀ : T) (hF : ∀ a x, F a t₀ x = x) (l : List α) :
    ∀ x, composeSupportedMotions F l t₀ x = x := by
  induction l with
  | nil => exact fun _ => rfl
  | cons a l ih =>
    intro x
    change F a t₀ (composeSupportedMotions F l t₀ x) = x
    rw [hF, ih]

omit [TopologicalSpace T] in
theorem composeSupportedMotions_eqOn_compl
    (F : α → T → X ≃ₜ X) (U : α → Set X)
    (hfix : ∀ a t, EqOn (F a t) id (U a)ᶜ) (l : List α) (t : T) :
    EqOn (composeSupportedMotions F l t) id (⋃ a ∈ l, U a)ᶜ := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro x hx
    have hxa : x ∉ U a := fun h => hx (mem_iUnion.mpr
      ⟨a, mem_iUnion.mpr ⟨List.mem_cons_self, h⟩⟩)
    have hxl : x ∉ ⋃ b ∈ l, U b := by
      intro h
      obtain ⟨b, hb, hxU⟩ := mem_iUnion₂.mp h
      exact hx (mem_iUnion₂.mpr ⟨b, List.mem_cons_of_mem a hb, hxU⟩)
    change F a t (composeSupportedMotions F l t x) = x
    rw [ih hxl]
    exact hfix a t hxa

omit [TopologicalSpace T] in
theorem composeSupportedMotions_eqOn_support
    (F : α → T → X ≃ₜ X) (U : α → Set X)
    (hfix : ∀ a t, EqOn (F a t) id (U a)ᶜ)
    (hdis : Pairwise (fun a b => Disjoint (U a) (U b)))
    (l : List α) (hl : l.Nodup) (t : T) :
    ∀ a ∈ l, EqOn (composeSupportedMotions F l t) (F a t) (U a) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨hal, hln⟩ := List.nodup_cons.mp hl
    intro b hb x hx
    rcases List.mem_cons.mp hb with heq | hb
    · subst b
      have hxl : x ∉ ⋃ b ∈ l, U b := by
        intro h
        obtain ⟨b, hb, hxB⟩ := mem_iUnion₂.mp h
        exact disjoint_left.mp (hdis (show a ≠ b from
          fun heq => hal (heq.symm ▸ hb))) hx hxB
      change F a t (composeSupportedMotions F l t x) = F a t x
      rw [composeSupportedMotions_eqOn_compl F U hfix l t hxl]
      rfl
    · have hba : b ≠ a := fun heq => hal (heq ▸ hb)
      have hm : F b t x ∈ U b := supported_homeomorph_mapsTo (F b t) (hfix b t) hx
      have hnot : F b t x ∉ U a := fun h => disjoint_left.mp (hdis hba) hm h
      change F a t (composeSupportedMotions F l t x) = F b t x
      rw [ih hln b hb hx]
      exact hfix a t hnot

end Geometry
