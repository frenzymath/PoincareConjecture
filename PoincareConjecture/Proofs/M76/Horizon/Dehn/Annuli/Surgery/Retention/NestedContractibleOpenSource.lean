import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.NestedPlanarComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OpenSourceCopy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedFibers

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)




theorem exists_nested_contractible_open_source
    {X : Type*} (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (hcontract : closure B₀.outer.inside ⊆ interior J.space)
    (hnest : closure B₁.outer.inside ⊆ B₀.inner.inside) (hd : 0 < d)
    (H : closure B₁.inner.inside ≃ₜ closure B₀.inner.inside) (hH : H.IsFinitePL)
    (f g : P2 → X) (hkeep : ∀ x : closure B₁.inner.inside, g (H x) = f x)
    (hout : EqOn g f (J.space \ B₀.outer.inside))
    (hsingle : ∀ z ∈ A₀, ∀ w ∈ J.space, g w = g z → w = z)
    (tube : Set X) (hpre : J.space ∩ f ⁻¹' tube = A₀ ∪ A₁)
    (hgA : g '' A₀ ⊆ tube)
    (htrace₀ : ∀ p : squareAnnulus L d,
      (B₀.chart p : P2) ∈ doubleLocusOn f J.space → depth L p = 0)
    (htrace₁ : ∀ p : squareAnnulus L d,
      (B₁.chart p : P2) ∈ doubleLocusOn f J.space → depth L p = 0) :
    let K := closure B₁.inner.inside ∪ (J.space \ B₀.outer.inside)
    ∃ (copy : K → P2) (U V : Set P2) (F : U ≃ₜ V),
      K ⊆ J.space ∧ Function.Injective copy ∧ Continuous copy ∧
      (∃ p : P2 → P2, FinitePiecewiseAffineOn p K ∧ ∀ x : K, p x = copy x) ∧
      (∀ x, copy x ∈ J.space) ∧ (∀ x, g (copy x) = f x) ∧
      (∀ x, copy x ∈ frontier J.space ↔ (x : P2) ∈ frontier J.space) ∧
      {v : P2 × P2 | v.1 ∈ J.space ∧ v.2 ∈ J.space ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        (fun v : K × K ↦ (copy v.1, copy v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} ∧
      doubleLocusOn g J.space =
        copy '' {x : K | ∃ y : K, f x = f y ∧ (x : P2) ≠ y} ∧
      U ⊆ K ∧ V ⊆ J.space ∧
      IsOpen ((Subtype.val : J.space → P2) ⁻¹' U) ∧
      IsOpen ((Subtype.val : J.space → P2) ⁻¹' V) ∧
      (∀ x : U, ∃ hx : (x : P2) ∈ K, (F x : P2) = copy ⟨x, hx⟩) ∧
      (∀ x : U, g (F x) = f x) ∧
      (∀ x : K, (x : P2) ∈ doubleLocusOn f J.space → (x : P2) ∈ U) ∧
      doubleLocusOn g J.space ⊆ V := by
  dsimp only
  let K := closure B₁.inner.inside ∪ (J.space \ B₀.outer.inside)
  let Band := closure B₀.outer.inside \ B₁.inner.inside
  obtain ⟨copy, hKS, hci, hcc, hcmaps, hckeep, hcfront, _, _, hcover, hrel, hnew, hPL⟩ :=
    exists_nested_contractible_retained_copy J hJ B₀ B₁ hcontract hnest H hH f g
      hkeep hout hsingle
  have hK : IsCompact K := hPL.choose_spec.1.isCompact
  have hA : IsClosed A₀ := B₀.chart_PL.symm.choose_spec.1.isCompact.isClosed
  obtain ⟨hBand, holdcover, havoid⟩ := nested_planar_retained_closed_band
    (S := J.space) B₀ B₁ hd hd htrace₀ htrace₁
  have hAB : A₀ ∪ A₁ ⊆ Band := by
    intro x hx
    rcases hx with hx | hx
    · refine ⟨(B₀.carrier.subset hx).1, ?_⟩
      intro hh
      exact (B₀.carrier.subset hx).2
        (hnest (subset_closure (B₁.nested (subset_closure hh))))
    · exact ⟨subset_closure (B₀.nested (subset_closure (hnest (B₁.carrier.subset hx).1))),
        (B₁.carrier.subset hx).2⟩
  have hcontact : ∀ x : K, copy x ∈ A₀ → (x : P2) ∈ Band := by
    intro x hx
    have hftube : f x ∈ tube := (hckeep x) ▸ hgA (mem_image_of_mem g hx)
    exact hAB (hpre.subset ⟨hKS x.property, hftube⟩)
  obtain ⟨U, V, F, hUK, hVS, hU, hV, hF, hFkeep, hcontains, hnewV⟩ :=
    exists_retained_open_source_copy hKS hK hBand hA copy hci hcc hcmaps hckeep
      holdcover hcover.symm.subset hcontact
      (fun x hx hb ↦ disjoint_left.mp havoid ⟨x.property, hx⟩ hb) hnew
  exact ⟨copy, U, V, F, hKS, hci, hcc, hPL, hcmaps, hckeep, hcfront, hrel, hnew,
    hUK, hVS, hU, hV, hF, hFkeep, hcontains, hnewV⟩

end PoincareConjecture.M76.Dehn.Annuli
