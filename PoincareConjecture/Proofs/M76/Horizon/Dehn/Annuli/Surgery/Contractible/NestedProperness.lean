import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedMap



set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_nested_contractible_proper_map
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A : Fin 2 → Set P2} {L d b : ℝ}
    (B : ∀ k, OrientedPolygonCollar L d (A k))
    (hcontract : closure (B 0).outer.inside ⊆ interior J.space)
    (hnest : closure (B 1).outer.inside ⊆ (B 0).inner.inside)
    (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f J.space)
    (R : Set X) (hin : MapsTo f J.space R)
    (hfront : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hτR : τ '' identityTube L d ⊆ interior R)
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f ((B k).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s))
    (hpreimage : J.space ∩ f ⁻¹' (τ '' identityTube L d) = A 0 ∪ A 1) :
    ∃ (H : closure (B 1).inner.inside ≃ₜ closure (B 0).inner.inside)
      (copy : P2 → P2) (a g : P2 → X),
      H.IsFinitePL ∧ FinitePiecewiseAffineOn copy (closure (B 1).inner.inside) ∧
      (∀ x : closure (B 1).inner.inside, copy x = (H x : P2)) ∧
      copy '' closure (B 1).inner.inside = closure (B 0).inner.inside ∧
      Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a p) ∧
      PolyhedralPLInCharts e a (squareAnnulus L d) ∧
      a '' squareAnnulus L d ⊆ τ '' identityTube L d ∧
      PolyhedralPLInCharts e g J.space ∧ MapsTo g J.space R ∧
      (∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      (∀ x : closure (B 1).inner.inside, g (copy x) = f x) ∧
      EqOn g f (J.space \ (B 0).outer.inside) ∧ EqOn g f (frontier J.space) ∧
      (∀ p : squareAnnulus L d, g ((B 0).chart p) = a p) ∧
      (∀ z ∈ A 0, ∀ w ∈ J.space, g w = g z → w = z) ∧
      g '' J.space = (f '' closure (B 1).inner.inside ∪
        f '' (J.space \ (B 0).outer.inside)) ∪ a '' squareAnnulus L d := by
  obtain ⟨H, copy, a, g, hH, hcopy, hcopyH, hcopyimage, hai, haPL, haTube,
    hgPL, hkeep, hout, hrim, hcollar, hsingle, himage⟩ :=
    exists_nested_contractible_map e hcompat J hJ B hcontract hnest
      hd hwidth hb hbd f hf τ hτ hfib hvalue hpreimage
  have hIint : closure (B 0).inner.inside ⊆ interior J.space :=
    (B 0).nested.trans (subset_closure.trans hcontract)
  have hQint : closure (B 1).inner.inside ⊆ interior J.space :=
    (B 1).nested.trans (subset_closure.trans
      (hnest.trans (subset_closure.trans hIint)))
  have hgI (x : closure (B 0).inner.inside) : g x = f (H.symm x) := by
    have hx : copy (H.symm x) = (x : P2) :=
      (hcopyH _).trans (congrArg Subtype.val (H.apply_symm_apply x))
    exact (congrArg g hx).symm.trans (hkeep (H.symm x))
  have hgin : MapsTo g J.space R := by
    intro x hx
    rcases himage.subset (mem_image_of_mem g hx) with (hQ | hO) | hA
    · obtain ⟨y, hy, heq⟩ := hQ
      exact heq ▸ hin (interior_subset (hQint hy))
    · obtain ⟨y, hy, heq⟩ := hO
      exact heq ▸ hin hy.1
    · exact interior_subset (hτR (haTube hA))
  have hgfront (x : P2) (hx : x ∈ J.space) :
      g x ∈ frontier R ↔ x ∈ frontier J.space := by
    by_cases hxP : x ∈ (B 0).outer.inside
    · have hxint : x ∈ interior J.space := hcontract (subset_closure hxP)
      have hxnot : x ∉ frontier J.space :=
        fun h ↦ disjoint_left.mp disjoint_interior_frontier hxint h
      apply iff_of_false ?_ hxnot
      by_cases hxI : x ∈ closure (B 0).inner.inside
      · rw [hgI ⟨x, hxI⟩]
        intro h
        have hyint := hQint (H.symm ⟨x, hxI⟩).property
        exact disjoint_left.mp disjoint_interior_frontier hyint
          ((hfront _ (interior_subset hyint)).mp h)
      · have hxA : x ∈ A 0 := (B 0).carrier.symm.subset
          ⟨subset_closure hxP, fun h ↦ hxI (subset_closure h)⟩
        let p := (B 0).chart.symm ⟨x, hxA⟩
        have hcp : ((B 0).chart p : P2) = x :=
          congrArg Subtype.val ((B 0).chart.apply_symm_apply _)
        have hga : g x = a p := (congrArg g hcp).symm.trans (hcollar p)
        rw [hga]
        exact fun h ↦ disjoint_left.mp disjoint_interior_frontier
          (hτR (haTube (mem_image_of_mem a p.property))) h
    · rw [hout ⟨hx, hxP⟩]
      exact hfront x hx
  exact ⟨H, copy, a, g, hH, hcopy, hcopyH, hcopyimage, hai, haPL, haTube,
    hgPL, hgin, hgfront, hkeep, hout, hrim, hcollar, hsingle, himage⟩

end PoincareConjecture.M76.Dehn.Annuli
