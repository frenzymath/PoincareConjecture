import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapGeometry
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Gluing.Frontier












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_chosen_cap_union_frontier
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    {r : ℝ} (hr : 0 < r) (positive : Bool)
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
    let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
    let A := ⋃ i, ⋃ (_ : occupied i),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    IsCompact A ∧ closure (interior A) = A ∧
      frontier A ⊆
        ((fun t : ℝ => H (0, t * r)) '' Icc (0 : ℝ) 1 ∪
          (fun t : ℝ => H (t * r, 0)) '' Icc (0 : ℝ) 1) ∪
        ⋃ i, ⋃ (_ : occupied i),
          (fun t : ℝ => F i ((1 - t) * r, t * r)) '' Icc (0 : ℝ) 1 := by
  classical
  dsimp only
  choose face hc hzero hone htwo hcoordinates using fun i =>
    m64Intrinsic_exists_coordinate_face_of_chosen_cap (F i) hr (hsource i) (hF i) (hFi i)
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let A := ⋃ i : {i : Bool × Bool // occupied i}, (face i).carrier
  have hA : A = ⋃ i, ⋃ (_ : occupied i),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} := by
    ext z
    simp only [A, mem_iUnion, Subtype.exists, hc]
  have hcompact : IsCompact A := isCompact_iUnion (fun i => (face i).isCompact_carrier_image)
  have hregular : closure (interior A) = A := by
    apply Poincare.Topology.closure_interior_iUnion_of_regular_closed
      (fun i : {i : Bool × Bool // occupied i} => (face i).carrier)
      (fun i => (face i).isClosed_carrier)
    intro i
    obtain ⟨C, b, _, _, hs, hcarrier, _⟩ := hcoordinates i
    rw [hcarrier]
    exact coordinate_triangle_closure_interior C b hs
  rw [← hA]
  refine ⟨hcompact, hregular, ?_⟩
  have ht {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t * r ∈ Icc (0 : ℝ) r :=
    ⟨mul_nonneg ht.1 hr.le, by nlinarith [ht.2]⟩
  have hsub (i : Bool × Bool) : (face i).carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) := by
    rw [hc]
    exact hsector i
  have hsecond' (i : Bool × Bool) (t : ℝ) (ht' : t ∈ Icc (0 : ℝ) 1) :
      ((face i).boundary 1).map t = H (sectorParameterEquiv 0 i (0, t * r)) := by
    rw [hone, hsecond i _ (ht ht')]
  have hfirst' (i : Bool × Bool) (t : ℝ) (ht' : t ∈ Icc (0 : ℝ) 1) :
      ((face i).boundary 2).map t = H (sectorParameterEquiv 0 i (t * r, 0)) := by
    rw [htwo, hfirst i _ (ht ht')]
  have hchord' (i : Bool × Bool) (t : ℝ) :
      ((face i).boundary 0).map t =
        (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
          t • H (sectorParameterEquiv 0 i (0, r)) := by
    rw [hzero, hchord, hfirst i r ⟨hr.le, le_rfl⟩,
      hsecond i r ⟨hr.le, le_rfl⟩]
  cases positive
  · let idx : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]
    have heq : A = ⋃ j : Fin 3, (face (idx j)).carrier := by
      ext z
      constructor
      · intro hz
        obtain ⟨⟨⟨i, j⟩, hij⟩, hi⟩ := mem_iUnion.mp hz
        cases i <;> cases j
        · exact mem_iUnion.mpr ⟨0, hi⟩
        · exact mem_iUnion.mpr ⟨1, hi⟩
        · exact mem_iUnion.mpr ⟨2, hi⟩
        · exact (hij rfl).elim
      · intro hz
        obtain ⟨j, hj⟩ := mem_iUnion.mp hz
        refine mem_iUnion.mpr ⟨⟨idx j, ?_⟩, hj⟩
        fin_cases j <;> decide
    rw [heq]
    have hfront := m64Intrinsic_reflex_corner_frontier_subset H r face hsub
      hsecond' hfirst' hchord' hcoordinates
    intro z hz
    rcases hfront hz with (hv | hh) | htop
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr hh)
    · obtain ⟨j, t, htr, htz⟩ := mem_iUnion.mp htop
      apply Or.inr
      refine mem_iUnion.mpr ⟨idx j, mem_iUnion.mpr ⟨?_, t, htr, ?_⟩⟩
      · fin_cases j <;> decide
      · exact (hzero (idx j) t).symm.trans htz
  · have heq : A = (face (true, true)).carrier := by
      ext z
      simp [A, occupied]
    rw [heq, (face (true, true)).boundary_carrier]
    intro z hz
    obtain ⟨k, t, htr, rfl⟩ := mem_iUnion.mp hz
    fin_cases k
    · apply Or.inr
      refine mem_iUnion.mpr ⟨(true, true), mem_iUnion.mpr ⟨rfl, t, htr, ?_⟩⟩
      exact (hzero (true, true) t).symm
    · apply Or.inl (Or.inl ?_)
      refine ⟨t, htr, ?_⟩
      change H (0, t * r) = ((face (true, true)).boundary 1).map t
      have h := (hsecond' (true, true) t htr).symm
      simp only [sectorParameterEquiv_apply, ↓reduceIte, Prod.fst_zero, Prod.snd_zero,
        add_zero] at h
      exact h
    · apply Or.inl (Or.inr ?_)
      refine ⟨t, htr, ?_⟩
      change H (t * r, 0) = ((face (true, true)).boundary 2).map t
      have h := (hfirst' (true, true) t htr).symm
      simp only [sectorParameterEquiv_apply, ↓reduceIte, Prod.fst_zero, Prod.snd_zero,
        add_zero] at h
      exact h

end PoincareConjecture
