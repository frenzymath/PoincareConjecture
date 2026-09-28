import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Anchor.Labels
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Decomposition







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




theorem exists_terminal_negative_anchors
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) {r η : Real} (hr : 0 < r) (hη : 0 < η)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - (x 0)^2 + (x 1)^2)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b a₀ b₀ : Fin 2 → Real)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (hrect : ∀ i, Icc (a i) (b i) ×ˢ Icc (-η) η ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ (F i).source →
      inner Real (M.v : E3) (g (F i z)) = inner Real (M.v : E3) (g p) + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcentral : (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      {q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} \ e '' openSquare r)
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)})
    (hband : (fun q => inner Real (M.v : E3) (g q)) ⁻¹'
      Icc (inner Real (M.v : E3) (g p) - η) (inner Real (M.v : E3) (g p) + η) ⊆
      e '' openSquare r ∪ ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η))
    (hfirst : ∀ i j : Fin 2 × Fin 2,
      e (contact r i) ∈ connectedComponentIn
        ({q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} \ e '' openSquare r)
        (e (contact r j)) ↔ i.1 = j.1) :
    ∃ (i : Fin 2) (κ : Real), 0 < κ ∧ κ < η ∧
      ∀ τ : Real, 0 < τ → τ < κ → τ < r^2 →
        ∃ α : S1 → S2, ContMDiff (𝓡 1) (𝓡 2) ∞ α ∧ Injective α ∧
          (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) α q)) ∧
          (∀ q, inner Real (M.v : E3) (g (α q)) = inner Real (M.v : E3) (g p) - τ) ∧
          negativePatchArc e r τ 1 ⊆ range α ∧
          range α ⊆ negativePatchArc e r τ 1 ∪ F i '' (Icc (a i) (b i) ×ˢ ({-τ} : Set Real)) := by
  obtain ⟨δ, L, A, B, hδ, hδη, _, hL, _, hrecut⟩ :=
    exists_recut_exterior_strips (h := fun q => inner Real (M.v : E3) (g q))
      e hr hrs hform F a b a₀ b₀ hη hchain hrect hheight hdisjoint hcentral hends hband
  have hsource₀ (i : Fin 2) : Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real) ⊆ (F i).source := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hrect i ⟨⟨(hchain i).1.le.trans hs.1, hs.2.trans (hchain i).2.2.le⟩,
      ⟨by linarith, hη.le⟩⟩
  have hpair (i j : Fin 2 × Fin 2) : (L.symm i).1 = (L.symm j).1 ↔ i.1 = j.1 :=
    (strip_label_eq_iff_component F a₀ b₀ (fun i => (hchain i).2.1.le) hsource₀
      hdisjoint hcentral L (fun j => e (contact r j)) hL i j).trans (hfirst i j)
  obtain ⟨ε, hε, hfamilies⟩ := M.exists_terminal_annular_end_family hg P hP hcaps hp hc
  let κ := min δ ε / 2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκδ : κ < δ := by dsimp [κ]; linarith [min_le_left δ ε]
  have hκε : κ < ε := by dsimp [κ]; linarith [min_le_right δ ε]
  refine ⟨(L.symm (1, 0)).1, κ, hκ, hκδ.trans hδη, ?_⟩
  intro τ hτ hτκ hτr
  obtain ⟨Ends, hcut, _⟩ := hfamilies τ hτ (hτκ.trans hκε).le
  have ht : -τ ∈ Icc (-δ) δ := ⟨by linarith, by linarith⟩
  have hdata := (hrecut (-τ) ht).1
  refine exists_negative_anchor_of_recut_strips Ends e hr hτ hτr hrs hform hcut
    F a b (fun i => A i (-τ)) (fun i => B i (-τ))
    (fun i => (hdata i).2.2.2.1.le) (fun i => (hdata i).2.2.2.2.2.1) hdisjoint
    ?_ L ?_ hpair ?_
  · simpa only [stripSlice, Set.preimage, mem_singleton_iff, sub_eq_add_neg]
      using (hrecut (-τ) ht).2.symm
  · rintro ⟨i, j⟩
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := hdata i
    fin_cases j
    · exact ha
    · exact hb
  · exact fun i => ⟨(hdata i).2.2.1.le, (hdata i).2.2.2.2.1.le⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

end

end M38Schoenflies
