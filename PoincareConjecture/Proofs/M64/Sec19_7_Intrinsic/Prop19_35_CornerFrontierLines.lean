import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnBandLines

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_retained_corner_frontier_lines
    {r : ℝ} (hr : 0 < r)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive : Bool)
    (hsource : ∀ i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (F i).source)
    (hFi : ∀ i, ContDiffOn ℝ ∞ (F i).symm (F i).target)
    (hfirst : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hchord : ∀ i t, F i ((1 - t) * r, t * r) =
      (1 - t) • F i (r, 0) + t • F i (0, r))
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    {K : Set AnnulusCoordinates}
    (haxes : (fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
      (fun t : ℝ => H (t * r, 0)) '' Icc 0 1 ⊆ K) :
    let C := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    IsCompact C ∧ closure (interior C) = C ∧
      ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
        (∀ l ∈ lines, Function.Surjective l) ∧
        frontier C ⊆ K ∪ ⋃ l ∈ lines, {z | l z = 0} := by
  classical
  obtain ⟨hcompact, hregular, hfront⟩ := m64Intrinsic_chosen_cap_union_frontier
    H F hr positive hsource hF hFi hfirst hsecond hchord hsector
  refine ⟨hcompact, hregular, ?_⟩
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let chord (i : {i : Bool × Bool // occupied i}) :=
    (fun t : ℝ => F i ((1 - t) * r, t * r)) '' Icc (0 : ℝ) 1
  obtain ⟨lines, hlines, hcover⟩ := exists_affine_lines_of_finite_segment_cover
    (fun i : {i : Bool × Bool // occupied i} => F i (r, 0))
    (fun i => F i (0, r)) (s := ⋃ i, chord i) (by
      intro z hz
      obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hz
      refine mem_iUnion.mpr ⟨i, ?_⟩
      dsimp only
      rw [hchord, segment_eq_image]
      exact ⟨t, ht, rfl⟩)
  refine ⟨lines, hlines, ?_⟩
  intro z hz
  rcases hfront hz with (hvertical | hhorizontal) | htop
  · exact Or.inl (haxes (Or.inl hvertical))
  · exact Or.inl (haxes (Or.inr hhorizontal))
  · right
    obtain ⟨i, hi⟩ := mem_iUnion.mp htop
    obtain ⟨hi, hz⟩ := mem_iUnion.mp hi
    exact hcover (mem_iUnion.mpr ⟨⟨i, hi⟩, hz⟩)

end PoincareConjecture
