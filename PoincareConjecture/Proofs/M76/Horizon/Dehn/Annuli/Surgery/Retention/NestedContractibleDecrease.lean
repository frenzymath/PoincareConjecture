import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.NestedPlanarComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.ComponentCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedFibers

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)



theorem nested_contractible_double_component_count_lt
    {X : Type*} (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (hcontract : closure B₀.outer.inside ⊆ interior J.space)
    (hnest : closure B₁.outer.inside ⊆ B₀.inner.inside) (hd : 0 < d)
    (H : closure B₁.inner.inside ≃ₜ closure B₀.inner.inside) (hH : H.IsFinitePL)
    (f g : P2 → X) (hkeep : ∀ x : closure B₁.inner.inside, g (H x) = f x)
    (hout : EqOn g f (J.space \ B₀.outer.inside))
    (hsingle : ∀ z ∈ A₀, ∀ w ∈ J.space, g w = g z → w = z)
    (M : SourceCircleDecomposition f J.space) (i k : M.Index)
    (hmiddle₀ : (fun p : squareAnnulus L d ↦ (B₀.chart p : P2)) ''
      {p | depth L p = 0} = M.pieces i)
    (hmiddle₁ : (fun p : squareAnnulus L d ↦ (B₁.chart p : P2)) ''
      {p | depth L p = 0} = M.pieces k)
    (htrace₀ : ∀ x ∈ A₀, x ∈ doubleLocusOn f J.space → x ∈ M.pieces i)
    (htrace₁ : ∀ x ∈ A₁, x ∈ doubleLocusOn f J.space → x ∈ M.pieces k) :
    Nat.card (ConnectedComponents (doubleLocusOn g J.space)) <
      Nat.card (ConnectedComponents (doubleLocusOn f J.space)) := by
  obtain ⟨hwhole, _, hremoved, _⟩ := M.nested_planar_component_retention i k
    B₀ B₁ hd hd hnest hmiddle₀ hmiddle₁ htrace₀ htrace₁
  obtain ⟨copy, hKS, hci, hcc, _, _, _, _, _, _, _, hnew, _⟩ :=
    exists_nested_contractible_retained_copy J hJ B₀ B₁ hcontract hnest H hH f g
      hkeep hout hsingle
  exact M.retained_component_count_lt hKS hwhole copy hci hcc hnew i hremoved

end PoincareConjecture.M76.Dehn.Annuli
