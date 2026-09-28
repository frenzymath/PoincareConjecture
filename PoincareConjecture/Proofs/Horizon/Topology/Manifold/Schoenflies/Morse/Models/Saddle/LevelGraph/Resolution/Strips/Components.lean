import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Components



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)


def stripSlice {M : Type*} [TopologicalSpace M]
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b : Fin 2 → Real) (t : Real) (i : Fin 2) : Set M :=
  F i '' (Icc (a i) (b i) ×ˢ ({t} : Set Real))

theorem stripSlice_geometry {M : Type*} [TopologicalSpace M]
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b : Fin 2 → Real) (t : Real) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({t} : Set Real) ⊆ (F i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target)) :
    (∀ i, IsCompact (stripSlice F a b t i) ∧ IsConnected (stripSlice F a b t i)) ∧
      Pairwise (fun i j => Disjoint (stripSlice F a b t i) (stripSlice F a b t j)) := by
  constructor
  · intro i
    refine ⟨(isCompact_Icc.prod isCompact_singleton).image_of_continuousOn
      ((F i).continuousOn.mono (hsource i)), ?_⟩
    exact ((isConnected_Icc (hab i)).prod isConnected_singleton).image
      (F i) ((F i).continuousOn.mono (hsource i))
  · intro i j hij
    exact (hdisjoint hij).mono ((F i).mapsTo.mono_left (hsource i)).image_subset
      ((F j).mapsTo.mono_left (hsource j)).image_subset


theorem contact_mem_stripSlice_iff {M : Type*} [TopologicalSpace M]
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b : Fin 2 → Real) (t : Real) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({t} : Set Real) ⊆ (F i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (q : Fin 2 × Fin 2 → M)
    (hends : ∀ k, F k.1 (stripEndpoint a b k, t) = q (L k))
    (j : Fin 2 × Fin 2) (i : Fin 2) :
    q j ∈ stripSlice F a b t i ↔ (L.symm j).1 = i := by
  have hown (k : Fin 2 × Fin 2) : q (L k) ∈ stripSlice F a b t k.1 := by
    refine ⟨(stripEndpoint a b k, t), ⟨?_, rfl⟩, hends k⟩
    unfold stripEndpoint
    split_ifs <;> exact ⟨by linarith [hab k.1], by linarith [hab k.1]⟩
  have hj : q j ∈ stripSlice F a b t (L.symm j).1 := by
    simpa only [L.apply_symm_apply] using hown (L.symm j)
  constructor
  · intro hi
    by_contra hn
    exact disjoint_left.mp ((stripSlice_geometry F a b t hab hsource hdisjoint).2 hn) hj hi
  · intro heq
    exact heq ▸ hj



theorem strip_label_eq_iff_component {M : Type*} [TopologicalSpace M] [T2Space M]
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b : Fin 2 → Real) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    {K : Set M} (hcover : (⋃ i, stripSlice F a b 0 i) = K)
    (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (q : Fin 2 × Fin 2 → M)
    (hends : ∀ k, F k.1 (stripEndpoint a b k, 0) = q (L k))
    (i j : Fin 2 × Fin 2) :
    (L.symm i).1 = (L.symm j).1 ↔ q i ∈ connectedComponentIn K (q j) := by
  have hg := stripSlice_geometry F a b 0 hab hsource hdisjoint
  exact Poincare.Topology.contact_index_eq_iff_mem_connectedComponentIn
    (stripSlice F a b 0) (fun i => (hg.1 i).1.isClosed)
    (fun i => (hg.1 i).2.isPreconnected) hg.2 hcover q (fun j => (L.symm j).1)
    (fun j => (contact_mem_stripSlice_iff F a b 0 hab hsource hdisjoint L q hends j _).mpr rfl) i j




theorem exists_resolved_level_components {M : Type*} [TopologicalSpace M] [T2Space M]
    {h : M → Real} {c r η : Real}
    (e : OpenPartialHomeomorph E2 M) (hr : 0 < r)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b a₀ b₀ : Fin 2 → Real) (hη : 0 < η)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (hrect : ∀ i, Icc (a i) (b i) ×ˢ Icc (-η) η ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcentral : (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {c}) \ e '' openSquare r)
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)})
    (hband : h ⁻¹' Icc (c - η) (c + η) ⊆ e '' openSquare r ∪
      ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η))
    (hpair : (∀ i j : Fin 2 × Fin 2,
      e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {c}) \ e '' openSquare r)
        (e (contact r j)) ↔ i.1 = j.1) ∨
      (∀ i j : Fin 2 × Fin 2,
      e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {c}) \ e '' openSquare r)
        (e (contact r j)) ↔ i.2 = j.2)) :
    ∃ δ : Real, 0 < δ ∧ δ < η ∧ δ < r ^ 2 ∧
      ((∀ t : Real, 0 < t → t ≤ δ →
          IsConnected (h ⁻¹' {c + t}) ∧
          Nat.card (ConnectedComponents (h ⁻¹' {c - t})) = 2 ∧
          ∃ C : Fin 2 → Set M,
            Pairwise (fun i j => Disjoint (C i) (C j)) ∧
            (∀ i, negativePatchArc e r t i ⊆ C i) ∧
            ∀ i q, q ∈ C i → connectedComponentIn (h ⁻¹' {c - t}) q = C i) ∨
       (∀ t : Real, 0 < t → t ≤ δ →
          IsConnected (h ⁻¹' {c - t}) ∧
          Nat.card (ConnectedComponents (h ⁻¹' {c + t})) = 2 ∧
          ∃ C : Fin 2 → Set M,
            Pairwise (fun i j => Disjoint (C i) (C j)) ∧
            (∀ i, positivePatchArc e r t i ⊆ C i) ∧
            ∀ i q, q ∈ C i → connectedComponentIn (h ⁻¹' {c + t}) q = C i)) := by
  classical
  obtain ⟨δ, L, A, B, hδ, hδη, hδr, hL, _, hdata⟩ :=
    exists_recut_exterior_strips e hr hrs hform F a b a₀ b₀ hη hchain hrect
      hheight hdisjoint hcentral hends hband
  let K (t : Real) := stripSlice F (fun i => A i t) (fun i => B i t) t
  let k (j : Fin 2 × Fin 2) := (L.symm j).1
  have hsource₀ (i : Fin 2) : Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real) ⊆ (F i).source := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hrect i ⟨⟨(hchain i).1.le.trans hs.1, hs.2.trans (hchain i).2.2.le⟩,
      by constructor <;> linarith⟩
  have hk (i j : Fin 2 × Fin 2) : k i = k j ↔
      e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {c}) \ e '' openSquare r)
        (e (contact r j)) :=
    strip_label_eq_iff_component F a₀ b₀ (fun i => (hchain i).2.1.le) hsource₀
      hdisjoint hcentral L (fun j => e (contact r j)) hL i j
  have hgeom (t : Real) (ht : t ∈ Icc (-δ) δ) :
      (∀ i, IsCompact (K t i) ∧ IsConnected (K t i)) ∧
        Pairwise (fun i j => Disjoint (K t i) (K t j)) := by
    apply stripSlice_geometry F (fun i => A i t) (fun i => B i t) t _ _ hdisjoint
    · intro i
      obtain ⟨_, _, _, hAB, _⟩ := (hdata t ht).1 i
      exact hAB.le
    · intro i
      obtain ⟨_, _, _, _, _, hs, _⟩ := (hdata t ht).1 i
      exact hs
  have hcover (t : Real) (ht : t ∈ Icc (-δ) δ) :
      (⋃ i, K t i) = (h ⁻¹' {c + t}) \ e '' openSquare r := (hdata t ht).2.symm
  have hcontact (t : Real) (ht : t ∈ Icc (-δ) δ) (j : Fin 2 × Fin 2) :
      e (movingContact r t j) ∈ K t (k j) := by
    apply (contact_mem_stripSlice_iff F (fun i => A i t) (fun i => B i t) t
      (fun i => ((hdata t ht).1 i).2.2.2.1.le)
      (fun i => ((hdata t ht).1 i).2.2.2.2.2.1)
      hdisjoint L (fun j => e (movingContact r t j)) ?_ j _).mpr rfl
    rintro ⟨i, l⟩
    obtain ⟨_, _, _, _, _, _, ha, hb, _⟩ := (hdata t ht).1 i
    fin_cases l
    · exact ha
    · exact hb
  refine ⟨δ, hδ, hδη, hδr, ?_⟩
  rcases hpair with hp | hp
  · left
    intro t ht htδ
    have htp : t ∈ Icc (-δ) δ := ⟨by linarith, htδ⟩
    have htn : -t ∈ Icc (-δ) δ := ⟨by linarith, by linarith⟩
    have htr := htδ.trans_lt hδr
    have hkfirst (i j : Fin 2 × Fin 2) : k i = k j ↔ i.1 = j.1 :=
      (hk i j).trans (hp i j)
    have hupper := positive_level_connected_of_first_pairing e hr ht htr hrs hform
      (K t) (fun i => ((hgeom t htp).1 i).2) (hcover t htp) k (hcontact t htp) hkfirst
    have hcovern : (⋃ i, K (-t) i) = (h ⁻¹' {c - t}) \ e '' openSquare r := by
      simpa only [sub_eq_add_neg] using hcover (-t) htn
    obtain ⟨E, hE, hEd, hcard⟩ := negative_level_two_components_of_first_pairing
      e hr ht htr hrs hform (K (-t)) (fun i => ((hgeom (-t) htn).1 i).1.isClosed)
      (fun i => ((hgeom (-t) htn).1 i).2) (hgeom (-t) htn).2 hcovern
      k (hcontact (-t) htn) hkfirst
    exact ⟨hupper, hcard, (fun i => negativePatchArc e r t i ∪ K (-t) (E i)),
      hEd, (fun _ => subset_union_left), hE⟩
  · right
    intro t ht htδ
    have htp : t ∈ Icc (-δ) δ := ⟨by linarith, htδ⟩
    have htn : -t ∈ Icc (-δ) δ := ⟨by linarith, by linarith⟩
    have htr := htδ.trans_lt hδr
    have hksecond (i j : Fin 2 × Fin 2) : k i = k j ↔ i.2 = j.2 :=
      (hk i j).trans (hp i j)
    have hcovern : (⋃ i, K (-t) i) = (h ⁻¹' {c - t}) \ e '' openSquare r := by
      simpa only [sub_eq_add_neg] using hcover (-t) htn
    have hlower := negative_level_connected_of_second_pairing e hr ht htr hrs hform
      (K (-t)) (fun i => ((hgeom (-t) htn).1 i).2) hcovern
      k (hcontact (-t) htn) hksecond
    obtain ⟨E, hE, hEd, hcard⟩ := positive_level_two_components_of_second_pairing
      e hr ht htr hrs hform (K t) (fun i => ((hgeom t htp).1 i).1.isClosed)
      (fun i => ((hgeom t htp).1 i).2) (hgeom t htp).2 (hcover t htp)
      k (hcontact t htp) hksecond
    exact ⟨hlower, hcard, (fun i => positivePatchArc e r t i ∪ K t (E i)),
      hEd, (fun _ => subset_union_left), hE⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
