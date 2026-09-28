import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.RetainedExteriors



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => (Set.prod Q (Icc (-1 : ℝ) 1) : Set (V2 × ℝ))
local notation "Left" => (Set.prod Q (Icc (-1 : ℝ) (-(1 / 2 : ℝ))) : Set (V2 × ℝ))
local notation "Middle" => (Set.prod Q (Icc (-(1 / 2 : ℝ)) 0) : Set (V2 × ℝ))
local notation "Right" => (Set.prod Q (Icc (0 : ℝ) 1) : Set (V2 × ℝ))

theorem resolving_three_piece_boundary_iff
    {E X : Type*} [TopologicalSpace E] {O I : Set E} {L d : ℝ}
    (outer : Cyl ≃ₜ O) (inner : Cyl ≃ₜ I)
    (copyO : O ≃ₜ Left) (copyA : squareAnnulus L d ≃ₜ Middle)
    (copyI : I ≃ₜ Right) (f : E → X) (a : P2 → X) (g : (V2 × ℝ) → X)
    (hvO : ∀ x : O, g (copyO x) = f x)
    (hvA : ∀ x : squareAnnulus L d, g (copyA x) = a x)
    (hvI : ∀ x : I, g (copyI x) = f x)
    (hheightO : ∀ x : O, (copyO x).val.2 = ((outer.symm x).val.2 - 3) / 4)
    (hheightI : ∀ x : I, (copyI x).val.2 = ((inner.symm x).val.2 + 1) / 2)
    {Z : Set X}
    (hO : ∀ x : O, f x ∈ Z ↔ (outer.symm x).val.2 = -1)
    (hA : ∀ x : squareAnnulus L d, a x ∉ Z)
    (hI : ∀ x : I, f x ∈ Z ↔ (inner.symm x).val.2 = 1) :
    ∀ x : Cyl, g x ∈ Z ↔ x.val.2 = -1 ∨ x.val.2 = 1 := by
  intro x
  by_cases hlo : x.val.2 ≤ -(1 / 2 : ℝ)
  · let y : O := copyO.symm ⟨x, x.property.1, x.property.2.1, hlo⟩
    have hxy : (copyO y : V2 × ℝ) = x := congrArg Subtype.val (copyO.apply_symm_apply _)
    change g x.val ∈ Z ↔ _
    rw [← hxy, hvO, hO, hheightO]
    constructor
    · intro h
      exact Or.inl (by rw [h]; norm_num)
    · rintro (h | h)
      · linarith
      · linarith [(outer.symm y).property.2.2]
  by_cases hhi : x.val.2 ≤ 0
  · let y : squareAnnulus L d := copyA.symm ⟨x, x.property.1, (lt_of_not_ge hlo).le, hhi⟩
    have hxy : (copyA y : V2 × ℝ) = x := congrArg Subtype.val (copyA.apply_symm_apply _)
    have hnot : g x.val ∉ Z := by rw [← hxy, hvA]; exact hA y
    constructor
    · exact fun h ↦ (hnot h).elim
    · rintro (h | h) <;> exfalso <;> linarith
  · let y : I := copyI.symm ⟨x, x.property.1, (lt_of_not_ge hhi).le, x.property.2.2⟩
    have hxy : (copyI y : V2 × ℝ) = x := congrArg Subtype.val (copyI.apply_symm_apply _)
    change g x.val ∈ Z ↔ _
    rw [← hxy, hvI, hI, hheightI]
    constructor
    · intro h
      exact Or.inr (by rw [h]; norm_num)
    · rintro (h | h)
      · linarith [(inner.symm y).property.2.1]
      · linarith

theorem retained_exterior_boundary_iff
    {X : Type*} {O I : Set P2} {L d : ℝ} (f : P2 → X) (Z : Set X)
    (hf : ∀ x ∈ squareAnnulus L d, f x ∈ Z ↔ depth L x = -d ∨ depth L x = d)
    (hOS : O ⊆ squareAnnulus L d) (hIS : I ⊆ squareAnnulus L d)
    (hOstrict : ∀ x : O, depth L x < d) (hIstrict : ∀ x : I, -d < depth L x)
    (outer : Cyl ≃ₜ O) (inner : Cyl ≃ₜ I)
    (houter : ∀ x : Cyl, x.val.2 = -1 ↔ depth L (outer x : P2) = -d)
    (hinner : ∀ x : Cyl, x.val.2 = 1 ↔ depth L (inner x : P2) = d) :
    (∀ x : O, f x ∈ Z ↔ (outer.symm x).val.2 = -1) ∧
      (∀ x : I, f x ∈ Z ↔ (inner.symm x).val.2 = 1) := by
  constructor
  · intro x
    have hh := houter (outer.symm x)
    rw [outer.apply_symm_apply] at hh
    rw [hf x (hOS x.property), hh]
    exact or_iff_left (ne_of_lt (hOstrict x))
  · intro x
    have hh := hinner (inner.symm x)
    rw [inner.apply_symm_apply] at hh
    rw [hf x (hIS x.property), hh]
    exact or_iff_right (ne_of_gt (hIstrict x))

end PoincareConjecture.M76.Dehn.Annuli
