import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.Disjoint.Properties










set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_disjoint_contractible_proper_map
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A : Fin 2 → Set P2} {L d b : ℝ} (B : ∀ k, OrientedPolygonCollar L d (A k))
    (hcontract : ∀ k, closure (B k).outer.inside ⊆ interior J.space)
    (hdis : Disjoint (closure (B 0).outer.inside) (closure (B 1).outer.inside))
    (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f J.space)
    (R : Set X) (hin : MapsTo f J.space R)
    (hfront : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hτR : τ '' identityTube L d ⊆ interior R)
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f ((B k).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s))
    (hpreimage : J.space ∩ f ⁻¹' (τ '' identityTube L d) = A 0 ∪ A 1) :
    ∃ (H : closure (B 0).inner.inside ≃ₜ closure (B 1).inner.inside)
      (a : Fin 2 → P2 → X) (g : P2 → X),
      H.IsFinitePL ∧
      (∀ x : closure (B 0).inner.inside,
        (H x : P2) ∈ (B 1).inner.boundary ℝ ↔ (x : P2) ∈ (B 0).inner.boundary ℝ) ∧
      (∀ k, Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a k p)) ∧
      (∀ k, PolyhedralPLInCharts e (a k) (squareAnnulus L d)) ∧
      (∀ k, a k '' squareAnnulus L d ⊆ τ '' identityTube L d) ∧
      Disjoint (a 0 '' squareAnnulus L d) (a 1 '' squareAnnulus L d) ∧
      PolyhedralPLInCharts e g J.space ∧ MapsTo g J.space R ∧
      (∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      (∀ x : closure (B 0).inner.inside, g (H x) = f x) ∧
      (∀ x : closure (B 1).inner.inside, g (H.symm x) = f x) ∧
      EqOn g f (J.space \ ((B 0).outer.inside ∪ (B 1).outer.inside)) ∧
      EqOn g f (frontier J.space) ∧
      (∀ k (p : squareAnnulus L d), g ((B k).chart p) = a k p) ∧
      (∀ z ∈ A 0 ∪ A 1, ∀ w ∈ J.space, g w = g z → w = z) ∧
      g '' J.space = ((f '' closure (B 0).inner.inside ∪ f '' closure (B 1).inner.inside) ∪
        f '' (J.space \ ((B 0).outer.inside ∪ (B 1).outer.inside))) ∪
          (a 0 '' squareAnnulus L d ∪ a 1 '' squareAnnulus L d) := by
  obtain ⟨H, a, g, hH, hHb, haemb, haPL, haTube, hadis, hg, hkeep0, hkeep1,
    hout, hrim, hcollar, himage⟩ := exists_disjoint_contractible_map e hcompat J hJ B
      hcontract hdis hd hwidth hb hbd f hf τ hτ hfib hvalue
  obtain ⟨hsingle, hgin, hgfront⟩ := disjoint_contractible_map_properties J hJ B hcontract hdis
    H hHb f g a (τ '' identityTube L d) R (fun k ↦ (haemb k).injective)
    haTube hadis hkeep0 hkeep1 hout hcollar hpreimage hin hfront hτR
  exact ⟨H, a, g, hH, hHb, haemb, haPL, haTube, hadis, hg, hgin, hgfront,
    hkeep0, hkeep1, hout, hrim, hcollar, hsingle, himage⟩

end PoincareConjecture.M76.Dehn.Annuli
