import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.Rims.RetainedReparametrization

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Ann" => squareAnnulus 8 1

theorem exists_corrected_retained_source
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {l r : ℝ} {A : Fin 2 → Set P2}
    {B : ∀ k, OrientedPolygonCollar l r (A k)} {j : Fin 2}
    {f : P2 → X} {τ : (P2 × ℝ) → X}
    (D : NestedResolvingCylinder (L := 8) (d := 1) e B j f τ)
    (H : Ann ≃ₜ Cyl) (hH : H.IsFinitePL) {G : P2 → X}
    (hG : ∀ x : Ann, G x = D.map (H x))
    (hr : 0 < r) (hnested : closure (B j.rev).outer.inside ⊆ (B j).inner.inside)
    (htrace : ∀ k (p : squareAnnulus l r),
      ((B k).chart p : P2) ∈ doubleLocusOn f Ann → depth l p = 0) :
    let O := annulusSquare 8 (-1) \ (B j).outer.inside
    let I := closure (B j.rev).inner.inside \ interior (annulusSquare 8 1)
    let K := O ∪ I
    ∃ (c₀ : K → Cyl) (c : K → P2) (U W : Set P2) (H₁ : U ≃ₜ W),
      (∀ x, c x = (H.symm (c₀ x) : P2)) ∧
      (∀ x : O, (c₀ ⟨x, Or.inl x.property⟩ : V2 × ℝ) = D.copyO x) ∧
      (∀ x : I, (c₀ ⟨x, Or.inr x.property⟩ : V2 × ℝ) = D.copyI x) ∧
      Function.Injective c ∧ Continuous c ∧
      (∃ J : P2 → P2, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = c x) ∧
      (∀ x, c x ∈ Ann) ∧ (∀ x, G (c x) = f x) ∧
      {v : P2 × P2 | v.1 ∈ Ann ∧ v.2 ∈ Ann ∧ G v.1 = G v.2 ∧ v.1 ≠ v.2} =
        (fun v : K × K ↦ (c v.1, c v.2)) '' {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} ∧
      doubleLocusOn G Ann = c '' {x : K | ∃ y : K, f x = f y ∧ (x : P2) ≠ y} ∧
      U ⊆ K ∧ W ⊆ Ann ∧
      IsOpen ((Subtype.val : Ann → P2) ⁻¹' U) ∧
      IsOpen ((Subtype.val : Ann → P2) ⁻¹' W) ∧
      (∀ x : U, ∃ hx : (x : P2) ∈ K, (H₁ x : P2) = c ⟨x, hx⟩) ∧
      (∀ x : U, G (H₁ x) = f x) ∧
      (∀ x : K, (x : P2) ∈ doubleLocusOn f Ann → (x : P2) ∈ U) ∧
      doubleLocusOn G Ann ⊆ W := by
  obtain ⟨c₀, U, V, H₀, hc₀i, hc₀c, hc₀PL, hc₀keep, hc₀O, hc₀I, _, hc₀maps,
    hc₀rel, _, hUK, hVT, hU, hV, hH₀, _, hcontains, hnew⟩ :=
      D.exists_retained_source hr hnested htrace
  obtain ⟨c, W, H₁, hcv, hci, hcc, hcPL, hcmaps, hckeep, hcrel, hcdouble,
    hWS, hW, hU', hH₁, hHkeep, hnew'⟩ := exists_reparametrized_retained_source
      H hH hG c₀ hc₀i hc₀c hc₀PL hc₀maps hc₀keep hc₀rel H₀ hVT hU hV hH₀ hnew
  exact ⟨fun x ↦ ⟨c₀ x, hc₀maps x⟩, c, U, W, H₁, hcv, hc₀O, hc₀I,
    hci, hcc, hcPL, hcmaps, hckeep, hcrel, hcdouble, hUK, hWS, hU', hW,
    hH₁, hHkeep, hcontains, hnew'⟩

end PoincareConjecture.M76.Dehn.Annuli.NestedResolvingCylinder
