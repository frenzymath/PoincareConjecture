import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.NestedCylinder
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.NestedOpenSource

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Left" => Set.prod Q (Icc (-1 : ℝ) (-(1 / 2 : ℝ)))
local notation "Right" => Set.prod Q (Icc (0 : ℝ) 1)

theorem exists_retained_source
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {l r L d : ℝ} {A : Fin 2 → Set P2}
    {B : ∀ k, OrientedPolygonCollar l r (A k)} {j : Fin 2}
    {f : P2 → X} {τ : (P2 × ℝ) → X}
    (D : NestedResolvingCylinder (L := L) (d := d) e B j f τ)
    (hr : 0 < r) (hnested : closure (B j.rev).outer.inside ⊆ (B j).inner.inside)
    (htrace : ∀ k (p : squareAnnulus l r),
      ((B k).chart p : P2) ∈ doubleLocusOn f (squareAnnulus L d) → depth l p = 0) :
    let O := annulusSquare L (-d) \ (B j).outer.inside
    let I := closure (B j.rev).inner.inside \ interior (annulusSquare L d)
    let K := O ∪ I
    ∃ (c : K → V2 × ℝ) (U : Set P2) (V : Set (V2 × ℝ)) (H : U ≃ₜ V),
      Function.Injective c ∧ Continuous c ∧
      (∃ J : P2 → V2 × ℝ, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = c x) ∧
      (∀ x, D.map (c x) = f x) ∧
      (∀ x : O, c ⟨x, Or.inl x.property⟩ = (D.copyO x : V2 × ℝ)) ∧
      (∀ x : I, c ⟨x, Or.inr x.property⟩ = (D.copyI x : V2 × ℝ)) ∧
      range c = Left ∪ Right ∧ (∀ x, c x ∈ Cyl) ∧
      {v : (V2 × ℝ) × (V2 × ℝ) |
        v.1 ∈ Cyl ∧ v.2 ∈ Cyl ∧ D.map v.1 = D.map v.2 ∧ v.1 ≠ v.2} =
        (fun v : K × K ↦ (c v.1, c v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} ∧
      doubleLocusOn D.map Cyl =
        c '' {x : K | ∃ y : K, f x = f y ∧ (x : P2) ≠ y} ∧
      U ⊆ K ∧ V ⊆ Cyl ∧
      IsOpen ((Subtype.val : squareAnnulus L d → P2) ⁻¹' U) ∧
      IsOpen ((Subtype.val : Cyl → V2 × ℝ) ⁻¹' V) ∧
      (∀ x : U, ∃ hx : (x : P2) ∈ K, (H x : V2 × ℝ) = c ⟨x, hx⟩) ∧
      (∀ x : U, D.map (H x) = f x) ∧
      (∀ x : K, (x : P2) ∈ doubleLocusOn f (squareAnnulus L d) → (x : P2) ∈ U) ∧
      doubleLocusOn D.map Cyl ⊆ V := by
  have hleft : Left = Set.prod Q (Icc (-1 : ℝ) (-1 / 2)) := by
    congr 2
    ring
  let copyO := D.copyO.trans (Homeomorph.setCongr hleft)
  have hcopyO : copyO.IsFinitePL := D.copyO_PL.setCongr rfl hleft
  have hsingle : ∀ z ∈ Set.prod Q (Icc (-1 / 2 : ℝ) 0),
      ∀ w ∈ Cyl, D.map w = D.map z → w = z := by
    have heq : Set.prod Q (Icc (-1 / 2 : ℝ) 0) =
        Set.prod Q (Icc (-(1 / 2 : ℝ)) 0) := by
      congr 2
      ring
    simpa only [heq] using D.middle_singleton
  have h := exists_nested_retained_open_source (B j) (B j.rev) hr hr hnested
    (htrace j) (htrace j.rev) D.outer D.inner copyO D.copyI hcopyO D.copyI_PL
    D.outer_source D.inner_source D.outer_contact D.inner_contact
    D.copyO_level D.copyI_level D.keepO D.keepI hsingle
  have hcopyval (x) : (copyO x : V2 × ℝ) = D.copyO x := rfl
  simpa only [← hleft, hcopyval] using h

end PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder
