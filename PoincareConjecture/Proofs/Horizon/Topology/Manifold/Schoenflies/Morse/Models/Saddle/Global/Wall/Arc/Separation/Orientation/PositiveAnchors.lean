import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Anchor.Terminal








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation

open SaddleLevel SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1



theorem exists_positive_anchor_with_contact_label
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C)
    (e : OpenPartialHomeomorph E2 S2) {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r^2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, inner Real v (g (e x)) = c - (x 0)^2 + (x 1)^2)
    (hcut : A.upperCut = c + t)
    (K : Fin 2 → Set S2) (hKc : ∀ i, IsClosed (K i)) (hK : ∀ i, IsConnected (K i))
    (hKd : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hcover : (⋃ i, K i) = {q | inner Real v (g q) = c + t} \ e '' openSquare r)
    (k : Fin 2 × Fin 2 → Fin 2)
    (hcontact : ∀ j, e (movingContact r t j) ∈ K (k j))
    (hpair : ∀ i j, k i = k j ↔ i.2 = j.2) (i : Fin 2) :
    ∃ j : A.UpperCutIndex,
      range (A.upperCutCircle j) = positivePatchArc e r t i ∪ K (k (0, i)) := by
  obtain ⟨E, hE, hEd, hcard⟩ := positive_level_two_components_of_second_pairing
    e hr ht htr hrs hform K hKc hK hKd hcover k hcontact hpair
  have hlabel : E i = k (0, i) := by
    have hlocal : e (movingContact r t (0, i)) ∈ positivePatchArc e r t i := by
      rw [movingContact_eq_positive hr ht.le]
      exact positiveContact_mem_patchArc e hr htr _ _
    by_contra hn
    have hij : i ≠ E.symm (k (0, i)) := by
      intro heq
      exact hn ((congrArg E heq).trans (E.apply_symm_apply _))
    apply disjoint_left.mp (hEd hij) (Or.inl hlocal)
    exact Or.inr (by simpa only [E.apply_symm_apply] using hcontact (0, i))
  have hcard' : Nat.card (ConnectedComponents
      {q | inner Real v (g q) = A.upperCut}) = 2 := by rwa [hcut]
  have hE' (j : Fin 2) (q : S2)
      (hq : q ∈ positivePatchArc e r t j ∪ K (E j)) :
      connectedComponentIn {q | inner Real v (g q) = A.upperCut} q =
        positivePatchArc e r t j ∪ K (E j) := by
    rw [hcut]
    exact hE j q hq
  obtain ⟨I, hI⟩ := A.exists_upperCutCircle_equiv_of_two_components hcard'
    (fun j => positivePatchArc e r t j ∪ K (E j)) hE' hEd
    (fun j => e (positiveLevelContact r t (j, 0)))
    (fun j => Or.inl (positiveContact_mem_patchArc e hr htr j 0))
  exact ⟨I i, by simpa only [hlabel] using hI i⟩



theorem exists_positive_anchor_of_recut_strips
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C)
    (e : OpenPartialHomeomorph E2 S2) {c r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r^2) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, inner Real v (g (e x)) = c - (x 0)^2 + (x 1)^2)
    (hcut : A.upperCut = c + t)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b l u : Fin 2 → Real) (hlu : ∀ i, l i ≤ u i)
    (hsource : ∀ i, Icc (l i) (u i) ×ˢ ({t} : Set Real) ⊆ (F i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcover : (⋃ i, stripSlice F l u t i) =
      {q | inner Real v (g q) = c + t} \ e '' openSquare r)
    (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hends : ∀ k, F k.1 (stripEndpoint l u k, t) = e (movingContact r t (L k)))
    (hpair : ∀ i j, (L.symm i).1 = (L.symm j).1 ↔ i.2 = j.2)
    (hinterval : ∀ i, a i ≤ l i ∧ u i ≤ b i) :
    ∃ j : A.UpperCutIndex,
      positivePatchArc e r t 1 ⊆ range (A.upperCutCircle j) ∧
      range (A.upperCutCircle j) ⊆ positivePatchArc e r t 1 ∪
        F (L.symm (0, 1)).1 '' (Icc (a (L.symm (0, 1)).1) (b (L.symm (0, 1)).1) ×ˢ
          ({t} : Set Real)) := by
  have hgeom := stripSlice_geometry F l u t hlu hsource hdisjoint
  obtain ⟨j, hrange⟩ := exists_positive_anchor_with_contact_label
    A e hr ht htr hrs hform hcut (stripSlice F l u t)
    (fun i => (hgeom.1 i).1.isClosed) (fun i => (hgeom.1 i).2) hgeom.2 hcover
    (fun j => (L.symm j).1)
    (fun j => (contact_mem_stripSlice_iff F l u t hlu hsource hdisjoint L
      (fun j => e (movingContact r t j)) hends j _).mpr rfl) hpair 1
  refine ⟨j, ?_, ?_⟩
  · rw [hrange]
    exact subset_union_left
  · rw [hrange]
    apply union_subset_union_right
    apply image_mono
    exact prod_mono (Icc_subset_Icc (hinterval _).1 (hinterval _).2) Subset.rfl



theorem exists_terminal_positive_anchors
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
    (hsecond : ∀ i j : Fin 2 × Fin 2,
      e (contact r i) ∈ connectedComponentIn
        ({q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} \ e '' openSquare r)
        (e (contact r j)) ↔ i.2 = j.2) :
    ∃ (i : Fin 2) (κ : Real), 0 < κ ∧ κ < η ∧
      ∀ τ : Real, 0 < τ → τ < κ → τ < r^2 →
        ∃ α : S1 → S2, ContMDiff (𝓡 1) (𝓡 2) ∞ α ∧ Injective α ∧
          (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) α q)) ∧
          (∀ q, inner Real (M.v : E3) (g (α q)) = inner Real (M.v : E3) (g p) + τ) ∧
          positivePatchArc e r τ 1 ⊆ range α ∧
          range α ⊆ positivePatchArc e r τ 1 ∪ F i '' (Icc (a i) (b i) ×ˢ ({τ} : Set Real)) := by
  obtain ⟨δ, L, A, B, hδ, hδη, _, hL, _, hrecut⟩ :=
    exists_recut_exterior_strips (h := fun q => inner Real (M.v : E3) (g q))
      e hr hrs hform F a b a₀ b₀ hη hchain hrect hheight hdisjoint hcentral hends hband
  have hsource₀ (i : Fin 2) : Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real) ⊆ (F i).source := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hrect i ⟨⟨(hchain i).1.le.trans hs.1, hs.2.trans (hchain i).2.2.le⟩,
      ⟨by linarith, hη.le⟩⟩
  have hpair (i j : Fin 2 × Fin 2) : (L.symm i).1 = (L.symm j).1 ↔ i.2 = j.2 :=
    (strip_label_eq_iff_component F a₀ b₀ (fun i => (hchain i).2.1.le) hsource₀
      hdisjoint hcentral L (fun j => e (contact r j)) hL i j).trans (hsecond i j)
  obtain ⟨ε, hε, hfamilies⟩ := M.exists_terminal_annular_end_family hg P hP hcaps hp hc
  let κ := min δ ε / 2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκδ : κ < δ := by dsimp [κ]; linarith [min_le_left δ ε]
  have hκε : κ < ε := by dsimp [κ]; linarith [min_le_right δ ε]
  refine ⟨(L.symm (0, 1)).1, κ, hκ, hκδ.trans hδη, ?_⟩
  intro τ hτ hτκ hτr
  obtain ⟨Ends, _, hcut⟩ := hfamilies τ hτ (hτκ.trans hκε).le
  have ht : τ ∈ Icc (-δ) δ := ⟨by linarith, by linarith⟩
  have hdata := (hrecut τ ht).1
  obtain ⟨j, hjlocal, hj⟩ := exists_positive_anchor_of_recut_strips Ends e hr hτ hτr hrs hform hcut
    F a b (fun i => A i τ) (fun i => B i τ)
    (fun i => (hdata i).2.2.2.1.le) (fun i => (hdata i).2.2.2.2.2.1) hdisjoint
    (by simpa only [stripSlice, Set.preimage, mem_singleton_iff] using (hrecut τ ht).2.symm)
    L (by
      rintro ⟨i, k⟩
      obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := hdata i
      fin_cases k
      · exact ha
      · exact hb) hpair
    (fun i => ⟨(hdata i).2.2.1.le, (hdata i).2.2.2.2.1.le⟩)
  obtain ⟨hs, hi, hd⟩ := Ends.upperCutCircle_geometry j
  exact ⟨Ends.upperCutCircle j, hs, hi, hd,
    fun q => (Ends.upperCutCircle_height j q).trans hcut, hjlocal, hj⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation
