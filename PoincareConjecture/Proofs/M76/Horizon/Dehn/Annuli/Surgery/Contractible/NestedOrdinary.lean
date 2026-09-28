import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedProperness
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.NestedContractibleOpenSource
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.NestedContractibleDecrease
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OrdinaryPreservation

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_nested_contractible_ordinary_map
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A : Fin 2 → Set P2} {L d b : ℝ} (B : ∀ k, OrientedPolygonCollar L d (A k))
    (hcontract : closure (B 0).outer.inside ⊆ interior J.space)
    (hnest : closure (B 1).outer.inside ⊆ (B 0).inner.inside)
    (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f J.space)
    (R : Set X) (hin : MapsTo f J.space R)
    (hfront : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    (hcollision : Disjoint (doubleLocusOn f J.space) (frontier J.space))
    (hcross : ∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f J.space R x y))
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hτR : τ '' identityTube L d ⊆ interior R)
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f ((B k).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s))
    (hpreimage : J.space ∩ f ⁻¹' (τ '' identityTube L d) = A 0 ∪ A 1)
    (M : SourceCircleDecomposition f J.space) (i k : M.Index)
    (hmiddle₀ : (fun p : squareAnnulus L d ↦ ((B 0).chart p : P2)) ''
      {p | depth L p = 0} = M.pieces i)
    (hmiddle₁ : (fun p : squareAnnulus L d ↦ ((B 1).chart p : P2)) ''
      {p | depth L p = 0} = M.pieces k)
    (htrace₀ : ∀ x ∈ A 0, x ∈ doubleLocusOn f J.space → x ∈ M.pieces i)
    (htrace₁ : ∀ x ∈ A 1, x ∈ doubleLocusOn f J.space → x ∈ M.pieces k) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g J.space ∧ MapsTo g J.space R ∧
      EqOn g f (frontier J.space) ∧
      (∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      Disjoint (doubleLocusOn g J.space) (frontier J.space) ∧
      IsCompact (doubleLocusOn g J.space) ∧
      (∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y → g x = g y →
        Nonempty (RawSourceCrossing e g J.space R x y)) ∧
      IsLocallyInjective (fun x : J.space ↦ g x) ∧
      Nonempty (SourceCircleDecomposition g J.space) ∧
      Nat.card (ConnectedComponents (doubleLocusOn g J.space)) <
        Nat.card (ConnectedComponents (doubleLocusOn f J.space)) := by
  obtain ⟨H, copy, a, g, hH, _, hcopyH, _, _, _, haTube, hg, hgin, hgfront,
    hcopykeep, hout, hrim, hcollar, hsingle, _⟩ :=
    exists_nested_contractible_proper_map e hcompat J hJ B hcontract hnest
      hd hwidth hb hbd f hf R hin hfront τ hτ hfib hτR hvalue hpreimage
  have hkeep (x : closure (B 1).inner.inside) : g (H x) = f x := by
    rw [← hcopyH x]
    exact hcopykeep x
  have hgA : g '' A 0 ⊆ τ '' identityTube L d := by
    rintro _ ⟨x, hx, rfl⟩
    let p := (B 0).chart.symm ⟨x, hx⟩
    have hp : ((B 0).chart p : P2) = x := congrArg Subtype.val ((B 0).chart.apply_symm_apply _)
    rw [← hp, hcollar]
    exact haTube (mem_image_of_mem a p.property)
  have hdepth₀ (p : squareAnnulus L d)
      (hp : ((B 0).chart p : P2) ∈ doubleLocusOn f J.space) : depth L p = 0 := by
    obtain ⟨q, hq, hqp⟩ := hmiddle₀.symm.subset (htrace₀ _ ((B 0).chart p).property hp)
    have he : q = p := (B 0).chart.injective (Subtype.ext hqp)
    exact he ▸ hq
  have hdepth₁ (p : squareAnnulus L d)
      (hp : ((B 1).chart p : P2) ∈ doubleLocusOn f J.space) : depth L p = 0 := by
    obtain ⟨q, hq, hqp⟩ := hmiddle₁.symm.subset (htrace₁ _ ((B 1).chart p).property hp)
    have he : q = p := (B 1).chart.injective (Subtype.ext hqp)
    exact he ▸ hq
  obtain ⟨j, U, V, F, hKS, hji, hjc, hjPL, _, hjkeep, hjfront, hrel, hnew,
    hUK, hVS, hU, hV, _, hFkeep, _, hcontains⟩ :=
    exists_nested_contractible_open_source J hJ (B 0) (B 1) hcontract hnest hd H hH f g
      hkeep hout hsingle (τ '' identityTube L d) hpreimage hgA hdepth₀ hdepth₁
  let E := Homeomorph.setCongr M.space
  let p := E.symm.trans (M.partner.trans E)
  have hpvalue (x : doubleLocusOn f J.space) : f (p x) = f x := M.value (E.symm x)
  have hpfree (x : doubleLocusOn f J.space) : (p x : P2) ≠ x := M.free (E.symm x)
  have hpunique (x : doubleLocusOn f J.space) (y : P2) (hy : y ∈ J.space)
      (hxy : f x = f y) (hne : (x : P2) ≠ y) : y = (p x : P2) :=
    M.unique (E.symm x) y hy hne hxy
  have hG : IsCompact (doubleLocusOn f J.space) := by
    rw [← M.space]
    exact M.graph.isCompact_space_of_finite M.finite
  have hS := J.isCompact_space_of_finite hJ
  obtain ⟨hnewCompact, hnewClosed, hnewInterior, hnewUnique, hnewCross, hlocal⟩ :=
    ordinary_crossings_preserved_by_retained_copy hKS hjPL.choose_spec.1.isCompact.isClosed
      hS hS hG p p.continuous hpvalue hpfree hpunique
      (double_image_interior_of_proper_rim hin hfront hcollision) hcross
      j hji hjc hjkeep hrel hnew (hUK.trans hKS) hVS hU hV
      hf.continuousOn hg.continuousOn F hFkeep hcontains
  have hnewCollision : Disjoint (doubleLocusOn g J.space) (frontier J.space) := by
    apply disjoint_left.mpr
    intro x hx hxfront
    obtain ⟨a, ⟨b, hab, hne⟩, rfl⟩ := hnew.subset hx
    exact disjoint_left.mp hcollision ⟨hKS a.property, b, hKS b.property, hab, hne⟩
      ((hjfront a).mp hxfront)
  have hmodel := nonempty_sourceCircleDecomposition hcompat J hJ hg hgin hnewClosed
    hnewInterior hnewCross hnewUnique
  exact ⟨g, hg, hgin, hrim, hgfront, hnewCollision, hnewCompact, hnewCross, hlocal, hmodel,
    nested_contractible_double_component_count_lt J hJ (B 0) (B 1) hcontract hnest hd H hH
      f g hkeep hout hsingle M i k hmiddle₀ hmiddle₁ htrace₀ htrace₁⟩

end PoincareConjecture.M76.Dehn.Annuli
