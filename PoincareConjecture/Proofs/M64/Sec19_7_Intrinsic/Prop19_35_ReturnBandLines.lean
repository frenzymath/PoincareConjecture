import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandBoundaryGeometry
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapUnionFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Affine.Lines













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane

namespace PoincareConjecture

section Bands

variable (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces
    (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
    lo a b ua wa ub wb ra rb)






theorem m64Intrinsic_linear_band_top_lines :
    ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧
      B.polygonalTop ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
  let v (k : Fin (B.interface.count + 1)) :=
    L (B.interface.cut k, lo (B.interface.cut k) + B.interface.height k)
  apply exists_affine_lines_of_finite_segment_cover
    (fun i : Fin B.interface.count => v i.castSucc) (fun i => v i.succ)
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  refine mem_iUnion.mpr ⟨i, ?_⟩
  change z ∈ (fun q : ℝ × ℝ => L (collarParameterEquiv
    (collarParameterEquiv.symm q))) '' _ at hi
  simp only [collarParameterEquiv.apply_symm_apply] at hi
  change z ∈ L.toLinearMap.toAffineMap '' _ at hi
  rw [image_segment] at hi
  exact hi






theorem m64Intrinsic_linear_band_frontier_lines :
    ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧
      frontier B.carrier ⊆ B.lowerArc ∪ ⋃ l ∈ lines, {z | l z = 0} := by
  obtain ⟨top, htop, htopsub⟩ := m64Intrinsic_linear_band_top_lines L B
  obtain ⟨left, hleft, hleftsub⟩ := exists_affine_line_containing_segment
    (L (a, lo a)) (L (a, lo a) + ra • L (ua, wa))
  obtain ⟨right, hright, hrightsub⟩ := exists_affine_line_containing_segment
    (L (b, lo b)) (L (b, lo b) + rb • L (ub, wb))
  refine ⟨left :: right :: top, ?_, ?_⟩
  · intro l hl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | rfl | hl
    · exact hleft
    · exact hright
    · exact htop l hl
  · intro z hz
    rw [B.frontier_carrier] at hz
    rcases hz with ((hlower | hupper) | hl) | hr
    · exact Or.inl hlower
    · right
      obtain ⟨l, hl⟩ := mem_iUnion.mp (htopsub hupper)
      obtain ⟨hl, hz⟩ := mem_iUnion.mp hl
      exact mem_iUnion.mpr ⟨l, mem_iUnion.mpr ⟨by simp [hl], hz⟩⟩
    · right
      rw [m64Intrinsic_band_left_cut L B] at hl
      exact mem_iUnion.mpr ⟨left, mem_iUnion.mpr ⟨by simp, hleftsub hl⟩⟩
    · right
      rw [m64Intrinsic_band_right_cut L B] at hr
      exact mem_iUnion.mpr ⟨right, mem_iUnion.mpr ⟨by simp, hrightsub hr⟩⟩

end Bands

open ChartCircleArrangementVertexPatch in





theorem m64Intrinsic_retained_caps_frontier_lines
    {gamma : ℝ → AnnulusCoordinates} {T r : ℝ} (hr : 0 < r) (hrT : r ≤ T)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive : Bool)
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
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
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2})) :
    let C := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    IsCompact C ∧ closure (interior C) = C ∧
      ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
        (∀ l ∈ lines, Function.Surjective l) ∧
        frontier C ⊆ gamma '' Icc 0 T ∪ ⋃ l ∈ lines, {z | l z = 0} := by
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
  · obtain ⟨t, ht, rfl⟩ := hvertical
    left
    dsimp only
    rw [haxis']
    refine ⟨T - t * r, ?_, rfl⟩
    constructor <;> nlinarith [ht.1, ht.2]
  · obtain ⟨t, ht, rfl⟩ := hhorizontal
    left
    dsimp only
    rw [haxis]
    refine ⟨t * r, ?_, rfl⟩
    constructor <;> nlinarith [ht.1, ht.2]
  · right
    obtain ⟨i, hi⟩ := mem_iUnion.mp htop
    obtain ⟨hi, hz⟩ := mem_iUnion.mp hi
    exact hcover (mem_iUnion.mpr ⟨⟨i, hi⟩, hz⟩)

end PoincareConjecture
