import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.Disjoint.Fibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.DisjointComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OpenSourceCopy

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_disjoint_contractible_open_source
    {X : Type*} (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (h₀ : closure B₀.outer.inside ⊆ interior J.space)
    (h₁ : closure B₁.outer.inside ⊆ interior J.space)
    (hdis : Disjoint (closure B₀.outer.inside) (closure B₁.outer.inside)) (hd : 0 < d)
    (H : closure B₀.inner.inside ≃ₜ closure B₁.inner.inside) (hH : H.IsFinitePL)
    (f g : P2 → X)
    (hkeep0 : ∀ x : closure B₀.inner.inside, g (H x) = f x)
    (hkeep1 : ∀ x : closure B₁.inner.inside, g (H.symm x) = f x)
    (hout : EqOn g f (J.space \ (B₀.outer.inside ∪ B₁.outer.inside)))
    (hsingle : ∀ z ∈ A₀ ∪ A₁, ∀ w ∈ J.space, g w = g z → w = z)
    (W : Set X) (hpre : J.space ∩ f ⁻¹' W = A₀ ∪ A₁) (hgA : g '' (A₀ ∪ A₁) ⊆ W)
    (M : SourceCircleDecomposition f J.space) (i k : M.Index)
    (hmiddle₀ : (fun p : squareAnnulus L d ↦ (B₀.chart p : P2)) ''
      {p | depth L p = 0} = M.pieces i)
    (hmiddle₁ : (fun p : squareAnnulus L d ↦ (B₁.chart p : P2)) ''
      {p | depth L p = 0} = M.pieces k)
    (htrace₀ : ∀ x ∈ A₀, x ∈ doubleLocusOn f J.space → x ∈ M.pieces i)
    (htrace₁ : ∀ x ∈ A₁, x ∈ doubleLocusOn f J.space → x ∈ M.pieces k) :
    let K := (closure B₀.inner.inside ∪ closure B₁.inner.inside) ∪
      (J.space \ (B₀.outer.inside ∪ B₁.outer.inside))
    ∃ (j : K → P2) (U V : Set P2) (F : U ≃ₜ V),
      K ⊆ J.space ∧ Function.Injective j ∧ Continuous j ∧ range j = K ∧
      (∃ p : P2 → P2, FinitePiecewiseAffineOn p K ∧ ∀ x : K, p x = j x) ∧
      (∀ x, g (j x) = f x) ∧
      (∀ x, j x ∈ frontier J.space ↔ (x : P2) ∈ frontier J.space) ∧
      {v : P2 × P2 | v.1 ∈ J.space ∧ v.2 ∈ J.space ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        (fun v : K × K ↦ (j v.1, j v.2)) ''
          {v | f v.1 = f v.2 ∧ (v.1 : P2) ≠ v.2} ∧
      doubleLocusOn g J.space = j '' {x : K | ∃ y : K, f x = f y ∧ (x : P2) ≠ y} ∧
      U ⊆ K ∧ V ⊆ J.space ∧
      IsOpen ((Subtype.val : J.space → P2) ⁻¹' U) ∧
      IsOpen ((Subtype.val : J.space → P2) ⁻¹' V) ∧
      (∀ x : U, ∃ hx : (x : P2) ∈ K, (F x : P2) = j ⟨x, hx⟩) ∧
      (∀ x : U, g (F x) = f x) ∧
      (∀ x : K, (x : P2) ∈ doubleLocusOn f J.space → (x : P2) ∈ U) ∧
      doubleLocusOn g J.space ⊆ V := by
  dsimp only
  let K := (closure B₀.inner.inside ∪ closure B₁.inner.inside) ∪
    (J.space \ (B₀.outer.inside ∪ B₁.outer.inside))
  obtain ⟨j, hKS, hji, hjc, hrange, hkeep, hfront, _, _, _, hcover, hrel, hnew, hPL⟩ :=
    exists_disjoint_contractible_retained_copy J hJ B₀ B₁ h₀ h₁ hdis H hH f g
      hkeep0 hkeep1 hout hsingle
  have hK : IsCompact K := hPL.choose_spec.1.isCompact
  have hA₀ : IsClosed A₀ := B₀.chart_PL.symm.choose_spec.1.isCompact.isClosed
  have hA₁ : IsClosed A₁ := B₁.chart_PL.symm.choose_spec.1.isCompact.isClosed
  obtain ⟨_, _, hselected, _, _⟩ := M.disjoint_planar_component_retention i k B₀ B₁ hd hd hdis
    hmiddle₀ hmiddle₁ htrace₀ htrace₁
  have havoid (x : K) (hx : (x : P2) ∈ doubleLocusOn f J.space) : (x : P2) ∉ A₀ ∪ A₁ := by
    intro h
    exact disjoint_left.mp hselected
      (h.elim (fun h ↦ Or.inl (htrace₀ x h hx)) (fun h ↦ Or.inr (htrace₁ x h hx))) x.property
  have hcontact (x : K) (hx : j x ∈ A₀ ∪ A₁) : (x : P2) ∈ A₀ ∪ A₁ := by
    have hfx : f x ∈ W := (hkeep x) ▸ hgA (mem_image_of_mem g hx)
    exact hpre.subset ⟨hKS x.property, hfx⟩
  have holdcover : J.space ⊆ K ∪ (A₀ ∪ A₁) := by
    dsimp only [K]
    rw [← hrange]
    exact hcover.symm.subset
  obtain ⟨U, V, F, hUK, hVS, hU, hV, hF, hFkeep, hcontains, hnewV⟩ :=
    exists_retained_open_source_copy hKS hK (hA₀.union hA₁) (hA₀.union hA₁)
      j hji hjc (fun x ↦ hKS (hrange.subset (mem_range_self x))) hkeep
      holdcover hcover.symm.subset hcontact havoid hnew
  exact ⟨j, U, V, F, hKS, hji, hjc, hrange, hPL, hkeep, hfront, hrel, hnew,
    hUK, hVS, hU, hV, hF, hFkeep, hcontains, hnewV⟩

end PoincareConjecture.M76.Dehn.Annuli
