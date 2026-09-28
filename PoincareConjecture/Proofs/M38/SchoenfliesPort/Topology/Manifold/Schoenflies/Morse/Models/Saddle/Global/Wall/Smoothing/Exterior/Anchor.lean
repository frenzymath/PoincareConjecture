import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Components
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ResolutionCircles
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ProjectedResolution

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

open SaddleLevel SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_negative_anchor_circles_of_first_pairing
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hv : ‖v‖ = 1) (e : OpenPartialHomeomorph E2 S2) {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, inner Real v (g (e x)) = c - x 0 ^ 2 + x 1 ^ 2)
    (hcut : A.lowerCut = c - t)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (hproj : ∀ x ∈ closedSquare r, planarProjection J (D (g (e x))) = x)
    (K : Fin 2 → Set S2) (hKc : ∀ i, IsClosed (K i)) (hK : ∀ i, IsConnected (K i))
    (hKd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hcover : (⋃ i, K i) = {q | inner Real v (g q) = c - t} \ e '' openSquare r)
    (k : Fin 2 × Fin 2 → Fin 2)
    (hcontact : ∀ j, e (movingContact r (-t) j) ∈ K (k j))
    (hpair : ∀ i j, k i = k j ↔ i.1 = j.1) :
    ∃ (E : Fin 2 ≃ Fin 2) (I : Fin 2 ≃ A.LowerCutIndex),
      ∀ i : Fin 2,
        _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
          (A.lowerProjectedCutCircle J D (I i)) ∧
        range (A.lowerProjectedCutCircle J D (I i)) =
          negativeLevelArc t i '' Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) ∪
            (fun q => planarProjection J (D (g q))) '' K (E i) := by
  obtain ⟨E, hE, hEd, hcard⟩ := negative_level_two_components_of_first_pairing
    e hr ht htr hrs hform K hKc hK hKd hcover k hcontact hpair
  have hcard' : Nat.card (ConnectedComponents
      {q | inner Real v (g q) = A.lowerCut}) = 2 := by
    rw [hcut]
    exact hcard
  have hE' (i : Fin 2) (q : S2)
      (hq : q ∈ negativePatchArc e r t i ∪ K (E i)) :
      connectedComponentIn {q | inner Real v (g q) = A.lowerCut} q =
        negativePatchArc e r t i ∪ K (E i) := by
    rw [hcut]
    exact hE i q hq
  obtain ⟨I, hI⟩ := A.exists_lowerCutCircle_equiv_of_two_components hcard'
    (fun i => negativePatchArc e r t i ∪ K (E i)) hE' hEd
    (fun i => e (negativeLevelContact r t (i, 0)))
    (fun i => Or.inl (negativeContact_mem_patchArc e hr htr i 0))
  refine ⟨E, I, fun i => ⟨A.lowerProjectedCutCircle_isSmoothEmbedding hg hv J D hDheight
    (I i), ?_⟩⟩
  let P : S2 → E2 := fun q => planarProjection J (D (g q))
  have hlocal : P '' negativePatchArc e r t i =
      negativeLevelArc t i '' Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) := by
    apply Subset.antisymm
    · rintro x ⟨q, ⟨u, hu, rfl⟩, rfl⟩
      change planarProjection J (D (g (e u))) ∈ _
      rwa [hproj u (negativeLevelArc_image_subset_square hr ht htr i hu)]
    · intro x hx
      exact ⟨e x, ⟨x, hx, rfl⟩,
        hproj x (negativeLevelArc_image_subset_square hr ht htr i hx)⟩
  calc
    range (A.lowerProjectedCutCircle J D (I i)) = P '' range (A.lowerCutCircle (I i)) :=
      range_comp P (A.lowerCutCircle (I i))
    _ = P '' (negativePatchArc e r t i ∪ K (E i)) := by rw [hI i]
    _ = _ := by rw [image_union, hlocal]

theorem exists_negative_anchor_circles_of_flattened_strips
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hv : ‖v‖ = 1) (e : OpenPartialHomeomorph E2 S2) {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, inner Real v (g (e x)) = c - x 0 ^ 2 + x 1 ^ 2)
    (hcut : A.lowerCut = c - t)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (hproj : ∀ x ∈ closedSquare r, planarProjection J (D (g (e x))) = x)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b : Fin 2 → Real) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({-t} : Set Real) ⊆ (F i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcover : (⋃ i, stripSlice F a b (-t) i) =
      {q | inner Real v (g q) = c - t} \ e '' openSquare r)
    (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hends : ∀ j, F j.1 (stripEndpoint a b j, -t) = e (movingContact r (-t) (L j)))
    (hpair : ∀ i j, (L.symm i).1 = (L.symm j).1 ↔ i.1 = j.1)
    (hflat : ∀ i s, s ∈ Icc (a i) (b i) →
      D (g (F i (s, -t))) = g (F i (s, 0)) + (-t) • v) :
    ∃ (E : Fin 2 ≃ Fin 2) (I : Fin 2 ≃ A.LowerCutIndex),
      ∀ i : Fin 2,
        _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
          (A.lowerProjectedCutCircle J D (I i)) ∧
        range (A.lowerProjectedCutCircle J D (I i)) =
          negativeLevelArc t i '' Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) ∪
            (fun s => planarProjection J (g (F (E i) (s, 0)))) '' Icc (a (E i)) (b (E i)) := by
  have hgeom := stripSlice_geometry F a b (-t) hab hsource hdisjoint
  obtain ⟨E, I, hI⟩ := exists_negative_anchor_circles_of_first_pairing A hg hv e
    hr ht htr hrs hform hcut J D hDheight hproj (stripSlice F a b (-t))
    (fun i => (hgeom.1 i).1.isClosed) (fun i => (hgeom.1 i).2) hgeom.2 hcover
    (fun j => (L.symm j).1)
    (fun j => (contact_mem_stripSlice_iff F a b (-t) hab hsource hdisjoint L
      (fun j => e (movingContact r (-t) j)) hends j _).mpr rfl) hpair
  have hproject (i : Fin 2) (s : Real) (hs : s ∈ Icc (a i) (b i)) :
      planarProjection J (D (g (F i (s, -t)))) = planarProjection J (g (F i (s, 0))) := by
    rw [hflat i s hs]
    simp [planarProjection]
  have hexterior (i : Fin 2) :
      (fun q => planarProjection J (D (g q))) '' stripSlice F a b (-t) i =
        (fun s => planarProjection J (g (F i (s, 0)))) '' Icc (a i) (b i) := by
    ext x
    constructor
    · rintro ⟨q, ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩, rfl⟩
      have hu' : u = -t := hu
      subst u
      exact ⟨s, hs, (hproject i s hs).symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨F i (s, -t), ⟨(s, -t), ⟨hs, rfl⟩, rfl⟩, hproject i s hs⟩
  exact ⟨E, I, fun i => ⟨(hI i).1, (hI i).2.trans (congrArg
    (fun K => negativeLevelArc t i ''
      Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) ∪ K) (hexterior (E i)))⟩⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

end

end M38Schoenflies
