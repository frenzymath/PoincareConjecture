import PoincareConjecture.Proofs.M76.Wall.OriginalExteriorPLDomains
import PoincareConjecture.Proofs.M76.Wall.OriginalExteriorFrontierImage











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in





theorem PLDomain.original_binary_exterior_domains
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L C W : Set X}
    (he : PLDomain e L) (hLC : L ⊆ C)
    (K N D : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hNK : N ≤ K) (hDK : D ≤ K)
    (H : C ≃ₜ K.space) (g : E → C) (hgc : ContinuousOn g K.space)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hFc : Continuous F) (hHF : ∀ y : C, (H y : E) = F y)
    (hN : N.space = F '' (C \ interior L)) (hD : D.space = F '' frontier L)
    (A : Set E) {h : E → ℝ} (hh : K.AffineOnFaces h)
    (hvalues : ∀ v ∈ K.vertices,
      (v ∈ A → h v = 1) ∧ (v ∉ A → h v = 0))
    (hstars : ∀ p ∈ A,
      ∃ G : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
        (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        G.source ⊆ interior C ∩ W ∧
        (G.source ⊆ Lᶜ ∨ ∃ (ell : V3 →L[ℝ] ℝ) (w : V3),
          ell w = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ ell (G y)) ∧
          ∀ y ∈ G.source, y ∈ frontier L ↔ ell (G y) = 0)) :
    let R := (fun z => (g z : X)) '' (N.space ∩ {z | (1 / 2 : ℝ) ≤ h z})
    IsCompact R ∧ R ⊆ interior C ∩ W ∧
      PLDomain e R ∧ PLDomain e (L ∪ R) ∧
      frontier R = (fun z => (g z : X)) ''
        ((N.space ∩ {z | h z = (1 / 2 : ℝ)}) ∪
          (D.space ∩ {z | (1 / 2 : ℝ) ≤ h z})) ∧
      frontier (L ∪ R) = (fun z => (g z : X)) ''
        ((D.space ∩ {z | h z ≤ (1 / 2 : ℝ)}) ∪
          (N.space ∩ {z | h z = (1 / 2 : ℝ)})) := by
  have hreg : ∀ v ∈ K.vertices, h v ≠ (1 / 2 : ℝ) := by
    intro v hv
    by_cases hvA : v ∈ A
    · rw [(hvalues v hv).1 hvA]
      norm_num
    · rw [(hvalues v hv).2 hvA]
      norm_num
  have hstars' : ∀ p ∈ K.vertices, p ∈ A →
      ∃ G : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
        (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        G.source ⊆ interior C ∩ W ∧
        (G.source ⊆ Lᶜ ∨ ∃ (psi : V3 →ᴬ[ℝ] ℝ) (w : V3),
          psi.contLinear w = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ psi (G y)) ∧
          ∀ y ∈ G.source, y ∈ frontier L ↔ psi (G y) = 0) := by
    intro p _ hp
    obtain ⟨G, hsource, hcoord, hcompat, hinside, hmodel⟩ := hstars p hp
    refine ⟨G, hsource, hcoord, hcompat, hinside, ?_⟩
    rcases hmodel with haway | ⟨ell, w, hw, hhalf, hfront⟩
    · exact Or.inl haway
    · exact Or.inr ⟨ell.toContinuousAffineMap, w, hw, hhalf, hfront⟩
  obtain ⟨hcompact, hinside, hnew, hunion, hfront, hfrontunion⟩ :=
    he.original_exterior_superlevel (beta := (1 / 2 : ℝ))
      hLC K N D hK hNK hDK H g hgc hg F hFc hHF
      hN hD A hh (fun v hv => (hvalues v hv).2) hstars' (by norm_num) hreg
  have hleft : LeftInvOn (fun z => (g z : X)) F C := by
    intro y hy
    have heq := hg (H ⟨y, hy⟩)
    rw [H.symm_apply_apply] at heq
    simpa only [hHF] using heq
  have himages := original_exterior_frontier_images he.closed hLC hleft
    hN hD hfront hfrontunion
  exact ⟨hcompact, hinside, hnew, hunion, himages⟩

end PoincareConjecture.M76
