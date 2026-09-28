import PoincareConjecture.Proofs.M76.Dehn.Mathlib.RelativeCompactPolyhedralNeighborhood

set_option autoImplicit false

open Set Module

namespace Geometry.SimplicialComplex

theorem exists_protected_face_carrier_within
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : SimplicialComplex ℝ E) (hP : P.faces.Finite) (t : Finset E)
    {Z : Set E} (hZ : IsClosed Z)
    {Ω : Set E} (hΩ : IsOpen Ω)
    (hZΩ : P.space ∩ Z ∩ convexHull ℝ (t : Set E) ⊆ Ω)
    (hlocal : ∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set E),
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ E),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set E) ∩ U, ∃ L ∈ Q, y ∈ L) :
    ∃ (P₀ : SimplicialComplex ℝ E) (V : Set P.space)
      (Q : Finset (AffineSubspace ℝ E)),
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧ IsOpen V ∧
      (Subtype.val ⁻¹' Z : Set P.space) ⊆ V ∧ Subtype.val '' V ⊆ P₀.space ∧
      (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
      (∀ x ∈ P₀.space ∩ convexHull ℝ (t : Set E), ∃ L ∈ Q, x ∈ L) ∧
      P₀.space ∩ convexHull ℝ (t : Set E) ⊆ Ω := by
  classical
  have hPc := P.isCompact_space_of_finite hP
  have htclosed : IsClosed (convexHull ℝ (t : Set E)) :=
    (t.finite_toSet.isCompact_convexHull ℝ).isClosed
  let C := P.space ∩ Z ∩ convexHull ℝ (t : Set E)
  have hC : IsCompact C := (hPc.inter_right hZ).inter_right htclosed
  have hlocal' (x : C) : ∃ U : Set E, IsOpen U ∧ x.val ∈ U ∧ U ⊆ Ω ∧
      ∃ Q : Finset (AffineSubspace ℝ E),
        (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
        ∀ y ∈ P.space ∩ convexHull ℝ (t : Set E) ∩ U, ∃ L ∈ Q, y ∈ L := by
    obtain ⟨U, hU, hxU, Q, hQ, hcover⟩ := hlocal x x.property
    exact ⟨U ∩ Ω, hU.inter hΩ, ⟨hxU, hZΩ x.property⟩, inter_subset_right,
      Q, hQ, fun y hy => hcover y ⟨hy.1, hy.2.1⟩⟩
  choose N hN hxN hNΩ Q hQ hcover using hlocal'
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover N hN
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩)
  let O : Set E := ⋃ x ∈ s, N x
  have hO : IsOpen O := isOpen_iUnion (fun x => isOpen_iUnion (fun _ => hN x))
  let B : Set E := (P.space ∩ convexHull ℝ (t : Set E)) \ O
  have hBc : IsCompact B := (hPc.inter_right htclosed).inter_right hO.isClosed_compl
  let W : Set P.space := Subtype.val ⁻¹' Bᶜ
  have hW : IsOpen W := hBc.isClosed.isOpen_compl.preimage continuous_subtype_val
  have hZW : (Subtype.val ⁻¹' Z : Set P.space) ⊆ W := by
    intro x hx hxB
    exact hxB.2 (hs ⟨⟨x.property, hx⟩, hxB.1.2⟩)
  let : CompactSpace P.space := isCompact_iff_compactSpace.mp hPc
  have hZc : IsCompact (Subtype.val ⁻¹' Z : Set P.space) :=
    (hZ.preimage continuous_subtype_val).isCompact
  obtain ⟨P₀, V, hP₀, hP₀P, hV, hZV, hVP₀, hP₀W⟩ :=
    P.exists_relative_compact_polyhedral_neighborhood hP hZc hW hZW
  have hP₀O : P₀.space ∩ convexHull ℝ (t : Set E) ⊆ O := by
    rintro y ⟨hyP₀, hyt⟩
    by_contra hy
    exact hP₀W
      (show (⟨y, hP₀P hyP₀⟩ : P.space) ∈ Subtype.val ⁻¹' P₀.space from hyP₀)
      ⟨⟨hP₀P hyP₀, hyt⟩, hy⟩
  refine ⟨P₀, V, s.biUnion Q, hP₀, hP₀P, hV, hZV, hVP₀, ?_, ?_, ?_⟩
  · intro L hL
    obtain ⟨x, _, hxL⟩ := Finset.mem_biUnion.mp hL
    exact hQ x L hxL
  · rintro y ⟨hyP₀, hyt⟩
    have hyP := hP₀P hyP₀
    have hyO : y ∈ O := hP₀O ⟨hyP₀, hyt⟩
    obtain ⟨x, hxs, hyN⟩ := mem_iUnion₂.mp hyO
    obtain ⟨L, hL, hyL⟩ := hcover x y ⟨⟨hyP, hyt⟩, hyN⟩
    exact ⟨L, Finset.mem_biUnion.mpr ⟨x, hxs, hL⟩, hyL⟩
  · intro y hy
    obtain ⟨x, _, hyN⟩ := mem_iUnion₂.mp (hP₀O hy)
    exact hNΩ x hyN

theorem exists_protected_face_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : SimplicialComplex ℝ E) (hP : P.faces.Finite) (t : Finset E)
    {Z : Set E} (hZ : IsClosed Z)
    (hlocal : ∀ x ∈ P.space ∩ Z ∩ convexHull ℝ (t : Set E),
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        ∃ Q : Finset (AffineSubspace ℝ E),
          (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
          ∀ y ∈ P.space ∩ convexHull ℝ (t : Set E) ∩ U, ∃ L ∈ Q, y ∈ L) :
    ∃ (P₀ : SimplicialComplex ℝ E) (V : Set P.space)
      (Q : Finset (AffineSubspace ℝ E)),
      P₀.faces.Finite ∧ P₀.space ⊆ P.space ∧ IsOpen V ∧
      (Subtype.val ⁻¹' Z : Set P.space) ⊆ V ∧ Subtype.val '' V ⊆ P₀.space ∧
      (∀ L ∈ Q, finrank ℝ L.direction ≤ 1) ∧
      ∀ x ∈ P₀.space ∩ convexHull ℝ (t : Set E), ∃ L ∈ Q, x ∈ L := by
  classical
  obtain ⟨P₀, V, Q, hP₀, hP₀P, hV, hZV, hVP₀, hQ, hcover, _⟩ :=
    P.exists_protected_face_carrier_within hP t hZ isOpen_univ (subset_univ _) hlocal
  exact ⟨P₀, V, Q, hP₀, hP₀P, hV, hZV, hVP₀, hQ, hcover⟩

end Geometry.SimplicialComplex
