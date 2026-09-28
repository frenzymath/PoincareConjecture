import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Anchor

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

theorem exists_negative_anchor_source_circles_of_first_pairing
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
    (hpair : ∀ i j, k i = k j ↔ i.1 = j.1) :
    ∃ (E : Fin 2 ≃ Fin 2) (α : Fin 2 → S1 → S2), ∀ i,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (α i) ∧ Injective (α i) ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) (α i) q)) ∧
      (∀ q, inner Real v (g (α i q)) = c - t) ∧
      range (α i) = negativePatchArc e r t i ∪ K (E i) := by
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
  refine ⟨E, fun i => A.lowerCutCircle (I i), fun i => ?_⟩
  obtain ⟨hs, hi, hd⟩ := A.lowerCutCircle_geometry (I i)
  exact ⟨hs, hi, hd, fun q => (A.lowerCutCircle_height (I i) q).trans hcut, hI i⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

end

end M38Schoenflies
