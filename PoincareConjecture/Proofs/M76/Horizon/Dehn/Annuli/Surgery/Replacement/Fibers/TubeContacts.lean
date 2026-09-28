import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Fibers.SingleFibers

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



theorem resolving_middle_singleton_of_full_tube_preimage
    {E X : Type*} [TopologicalSpace E] {O I U A B : Set E} {D : Set P2}
    {f : E → X} {a : P2 → X} {g : (V2 × ℝ) → X} {tube : Set X}
    (outer : Cyl ≃ₜ O) (inner : Cyl ≃ₜ I)
    (copyO : O ≃ₜ Left) (copyA : D ≃ₜ Middle) (copyI : I ≃ₜ Right)
    (hOU : O ⊆ U) (hIU : I ⊆ U)
    (hpre : ∀ x ∈ U, f x ∈ tube ↔ x ∈ A ∪ B)
    (houter : ∀ x : Cyl, (outer x : E) ∈ A ∪ B ↔ x.val.2 = 1)
    (hinner : ∀ x : Cyl, (inner x : E) ∈ A ∪ B ↔ x.val.2 = -1)
    (hlevelO : ∀ x : O, (copyO x).val.2 = ((outer.symm x).val.2 - 3) / 4)
    (hlevelI : ∀ x : I, (copyI x).val.2 = ((inner.symm x).val.2 + 1) / 2)
    (ha : InjOn a D) (hO : ∀ x : O, g (copyO x) = f x)
    (hA : ∀ x : D, g (copyA x) = a x) (hI : ∀ x : I, g (copyI x) = f x)
    (hatube : a '' D ⊆ tube) :
    ∀ z ∈ Middle, ∀ w ∈ Cyl, g w = g z → w = z := by
  apply resolving_middle_singleton_fibers copyO copyA copyI ha hO hA hI hatube
  · intro x hx
    have hmem := (hpre x (hOU x.property)).mp hx
    have hseam := (houter (outer.symm x)).mp (by simpa using hmem)
    rw [hlevelO, hseam]
    norm_num
  · intro x hx
    have hmem := (hpre x (hIU x.property)).mp hx
    have hseam := (hinner (inner.symm x)).mp (by simpa using hmem)
    rw [hlevelI, hseam]
    norm_num

end PoincareConjecture.M76.Dehn.Annuli
