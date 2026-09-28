import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.RetainedExteriors

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Left" => Set.prod Q (Icc (-1 : ℝ) (-1 / 2))
local notation "Middle" => Set.prod Q (Icc (-1 / 2 : ℝ) 0)
local notation "Right" => Set.prod Q (Icc (0 : ℝ) 1)

theorem resolving_middle_injective
    {X : Type*} {B : Set P2} {a : P2 → X} {g : (V2 × ℝ) → X}
    (copy : B ≃ₜ Middle) (ha : InjOn a B)
    (hvalue : ∀ x : B, g (copy x) = a x) : InjOn g Middle := by
  intro x hx y hy hxy
  let u := copy.symm ⟨x, hx⟩
  let v := copy.symm ⟨y, hy⟩
  have huv : a u = a v := by
    rw [← hvalue u, ← hvalue v]
    simpa only [u, v, Homeomorph.apply_symm_apply] using hxy
  have heq : u = v := Subtype.ext (ha u.property v.property huv)
  have hh := congrArg (fun p : B ↦ (copy p : V2 × ℝ)) heq
  simpa only [u, v, Homeomorph.apply_symm_apply] using hh

theorem resolving_middle_singleton_fibers
    {E X : Type*} [TopologicalSpace E] {O I : Set E} {B : Set P2}
    {f : E → X} {a : P2 → X} {g : (V2 × ℝ) → X} {tube : Set X}
    (copyO : O ≃ₜ Left) (copyA : B ≃ₜ Middle) (copyI : I ≃ₜ Right)
    (ha : InjOn a B) (hO : ∀ x : O, g (copyO x) = f x)
    (hA : ∀ x : B, g (copyA x) = a x) (hI : ∀ x : I, g (copyI x) = f x)
    (hatube : a '' B ⊆ tube)
    (hcontactO : ∀ x : O, f x ∈ tube → (copyO x : V2 × ℝ).2 = -1 / 2)
    (hcontactI : ∀ x : I, f x ∈ tube → (copyI x : V2 × ℝ).2 = 0) :
    ∀ z ∈ Middle, ∀ w ∈ Cyl, g w = g z → w = z := by
  have hinj := resolving_middle_injective copyA ha hA
  intro z hz w hw hvalue
  have hztube : g z ∈ tube := by
    let u := copyA.symm ⟨z, hz⟩
    have hu := hatube (mem_image_of_mem a u.property)
    rw [← hA u] at hu
    simpa only [u, Homeomorph.apply_symm_apply] using hu
  have hwtube : g w ∈ tube := hvalue ▸ hztube
  have hwM : w ∈ Middle := by
    by_cases hlo : w.2 ≤ -1 / 2
    · have hwL : w ∈ Left := ⟨hw.1, hw.2.1, hlo⟩
      let x := copyO.symm ⟨w, hwL⟩
      have hfxtube : f x ∈ tube := by
        rw [← hO x]
        simpa only [x, Homeomorph.apply_symm_apply] using hwtube
      have ht := hcontactO x hfxtube
      simp only [x, Homeomorph.apply_symm_apply] at ht
      exact ⟨hw.1, by rw [ht]; exact ⟨le_rfl, by norm_num⟩⟩
    · by_cases hhi : 0 ≤ w.2
      · have hwR : w ∈ Right := ⟨hw.1, hhi, hw.2.2⟩
        let x := copyI.symm ⟨w, hwR⟩
        have hfxtube : f x ∈ tube := by
          rw [← hI x]
          simpa only [x, Homeomorph.apply_symm_apply] using hwtube
        have ht := hcontactI x hfxtube
        simp only [x, Homeomorph.apply_symm_apply] at ht
        exact ⟨hw.1, by rw [ht]; exact ⟨by norm_num, le_rfl⟩⟩
      · exact ⟨hw.1, (lt_of_not_ge hlo).le, (lt_of_not_ge hhi).le⟩
  exact hinj hwM hz hvalue

end PoincareConjecture.M76.Dehn.Annuli
