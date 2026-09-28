import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Anchor.Source
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Components







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

open SaddleLevel SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1




theorem exists_negative_anchor_with_contact_label
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C)
    (e : OpenPartialHomeomorph E2 S2) {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, inner Real v (g (e x)) = c - (x 0) ^ 2 + (x 1) ^ 2)
    (hcut : A.lowerCut = c - t)
    (K : Fin 2 → Set S2) (hKc : ∀ i, IsClosed (K i)) (hK : ∀ i, IsConnected (K i))
    (hKd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hcover : (⋃ i, K i) = {q | inner Real v (g q) = c - t} \ e '' openSquare r)
    (k : Fin 2 × Fin 2 → Fin 2)
    (hcontact : ∀ j, e (movingContact r (-t) j) ∈ K (k j))
    (hpair : ∀ i j, k i = k j ↔ i.1 = j.1) (i : Fin 2) :
    ∃ α : S1 → S2, ContMDiff (𝓡 1) (𝓡 2) ∞ α ∧ Injective α ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) α q)) ∧
      (∀ q, inner Real v (g (α q)) = c - t) ∧
      range α = negativePatchArc e r t i ∪ K (k (i, 0)) := by
  obtain ⟨E, hE, hEd, hcard⟩ := negative_level_two_components_of_first_pairing
    e hr ht htr hrs hform K hKc hK hKd hcover k hcontact hpair
  have hlabel : E i = k (i, 0) := by
    have hlocal : e (movingContact r (-t) (i, 0)) ∈ negativePatchArc e r t i := by
      rw [movingContact_eq_negative hr (neg_nonpos.mpr ht.le), neg_neg]
      exact negativeContact_mem_patchArc e hr htr _ _
    by_contra hn
    have hij : i ≠ E.symm (k (i, 0)) := by
      intro heq
      exact hn ((congrArg E heq).trans (E.apply_symm_apply _))
    apply disjoint_left.mp (hEd hij) (Or.inl hlocal)
    exact Or.inr (by simpa only [E.apply_symm_apply] using hcontact (i, 0))
  have hcard' : Nat.card (ConnectedComponents
      {q | inner Real v (g q) = A.lowerCut}) = 2 := by rwa [hcut]
  have hE' (j : Fin 2) (q : S2)
      (hq : q ∈ negativePatchArc e r t j ∪ K (E j)) :
      connectedComponentIn {q | inner Real v (g q) = A.lowerCut} q =
        negativePatchArc e r t j ∪ K (E j) := by
    rw [hcut]
    exact hE j q hq
  obtain ⟨I, hI⟩ := A.exists_lowerCutCircle_equiv_of_two_components hcard'
    (fun j => negativePatchArc e r t j ∪ K (E j)) hE' hEd
    (fun j => e (negativeLevelContact r t (j, 0)))
    (fun j => Or.inl (negativeContact_mem_patchArc e hr htr j 0))
  obtain ⟨hs, hi, hd⟩ := A.lowerCutCircle_geometry (I i)
  exact ⟨A.lowerCutCircle (I i), hs, hi, hd,
    fun q => (A.lowerCutCircle_height (I i) q).trans hcut, by simpa [hlabel] using hI i⟩



theorem exists_negative_anchor_of_recut_strips
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C)
    (e : OpenPartialHomeomorph E2 S2) {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, inner Real v (g (e x)) = c - (x 0) ^ 2 + (x 1) ^ 2)
    (hcut : A.lowerCut = c - t)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b l u : Fin 2 → Real) (hlu : ∀ i, l i ≤ u i)
    (hsource : ∀ i, Icc (l i) (u i) ×ˢ ({-t} : Set Real) ⊆ (F i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcover : (⋃ i, stripSlice F l u (-t) i) =
      {q | inner Real v (g q) = c - t} \ e '' openSquare r)
    (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hends : ∀ k, F k.1 (stripEndpoint l u k, -t) = e (movingContact r (-t) (L k)))
    (hpair : ∀ i j, (L.symm i).1 = (L.symm j).1 ↔ i.1 = j.1)
    (hinterval : ∀ i, a i ≤ l i ∧ u i ≤ b i) :
    ∃ α : S1 → S2, ContMDiff (𝓡 1) (𝓡 2) ∞ α ∧ Injective α ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) α q)) ∧
      (∀ q, inner Real v (g (α q)) = c - t) ∧
      negativePatchArc e r t 1 ⊆ range α ∧
      range α ⊆ negativePatchArc e r t 1 ∪
        F (L.symm (1, 0)).1 '' (Icc (a (L.symm (1, 0)).1) (b (L.symm (1, 0)).1) ×ˢ
          ({-t} : Set Real)) := by
  have hgeom := stripSlice_geometry F l u (-t) hlu hsource hdisjoint
  obtain ⟨α, hs, hi, hd, hh, hrange⟩ := exists_negative_anchor_with_contact_label
    A e hr ht htr hrs hform hcut (stripSlice F l u (-t))
    (fun i => (hgeom.1 i).1.isClosed) (fun i => (hgeom.1 i).2) hgeom.2 hcover
    (fun j => (L.symm j).1)
    (fun j => (contact_mem_stripSlice_iff F l u (-t) hlu hsource hdisjoint L
      (fun j => e (movingContact r (-t) j)) hends j _).mpr rfl) hpair 1
  refine ⟨α, hs, hi, hd, hh, ?_, ?_⟩
  · rw [hrange]
    exact subset_union_left
  · rw [hrange]
    apply union_subset_union_right
    apply image_mono
    exact prod_mono (Icc_subset_Icc (hinterval _).1 (hinterval _).2) Subset.rfl

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

end

end M38Schoenflies
