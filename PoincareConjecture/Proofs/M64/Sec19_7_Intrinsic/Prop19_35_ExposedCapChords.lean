import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapUnionFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.PolygonalCores














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture







theorem m64Intrinsic_retained_cap_exposed_chord
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : ℝ)
    (F : Bool × Bool → SmoothFace AnnulusCoordinates) (positive : Bool)
    (hsub : ∀ i, (F i).carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsecond : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((F i).boundary 1).map t =
      H (sectorParameterEquiv 0 i (0, t * r)))
    (hfirst : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((F i).boundary 2).map t =
      H (sectorParameterEquiv 0 i (t * r, 0)))
    (hchord : ∀ i t, ((F i).boundary 0).map t =
      (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
        t • H (sectorParameterEquiv 0 i (0, r)))
    (hcoordinates : ∀ i, ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
      (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      convexHull ℝ (range b) ⊆ C.source ∧
      (F i).carrier = C '' convexHull ℝ (range b) ∧
      ∀ k, ((F i).boundary k).map = C ∘
        affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) :
    let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
    let A := ⋃ i, ⋃ (_ : occupied i), (F i).carrier
    ∀ i, occupied i → frontier A ∩ (F i).carrier ⊆
      ((fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
        (fun t : ℝ => H (t * r, 0)) '' Icc 0 1) ∪
      ((F i).boundary 0).map '' Icc (0 : ℝ) 1 := by
  classical
  dsimp only
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let A := ⋃ i, ⋃ (_ : occupied i), (F i).carrier
  have hinto (i : Bool × Bool) (hi : occupied i) : (F i).carrier ⊆ A :=
    fun _ hz => mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hz⟩⟩
  have hshared (i j : Bool × Bool) (hi : occupied i) (hj : occupied j)
      (hij : i ≠ j) (k : Fin 3)
      (heq : EqOn ((F i).boundary k).map ((F j).boundary k).map (Icc (0 : ℝ) 1))
      {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      ((F i).boundary k).map t ∈ interior A := by
    obtain ⟨C, b, _, _, hb, hfc, hfb⟩ := hcoordinates i
    obtain ⟨D, c, _, _, hc, hgc, hgb⟩ := hcoordinates j
    apply interior_mono (union_subset (hinto i hi) (hinto j hj))
    exact m64Intrinsic_corner_shared_edge_mem_interior H (F i) (F j) C D b c
      hb hc hfc hgc hfb hgb hij (hsub i) (hsub j) k k heq ht
  intro i hi z hz
  have hfront : z ∈ frontier (F i).carrier :=
    ⟨subset_closure hz.2, fun h => hz.1.2 (interior_mono (hinto i hi) h)⟩
  rw [(F i).boundary_carrier] at hfront
  obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.mp hfront
  have hzero : H 0 ∈ (fun t : ℝ => H (0, t * r)) '' Icc 0 1 :=
    ⟨0, by simp, by dsimp only; rw [zero_mul]; rfl⟩
  fin_cases k
  · exact Or.inr ⟨t, ht, rfl⟩
  · change ((F i).boundary 1).map t ∈ _
    by_cases ht0 : t = 0
    · subst t
      rw [hsecond i 0 (by simp), zero_mul]
      change H (sectorParameterEquiv 0 i 0) ∈ _
      rw [sectorParameterEquiv_zero]
      exact Or.inl (Or.inl hzero)
    by_cases ht1 : t = 1
    · subst t
      right
      refine ⟨1, by simp, ?_⟩
      simp [hsecond i 1 (by simp), hchord]
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    rcases i with ⟨i, j⟩
    cases j
    · have hpositive : positive = false := by
        cases positive
        · rfl
        · simp at hi
      have hother : occupied (!i, false) := by simp [occupied, hpositive]
      have hne : (i, false) ≠ (!i, false) := by cases i <;> decide
      apply False.elim (hz.1.2 (hshared (i, false) (!i, false) hi hother hne 1 ?_ hti))
      intro s hs
      rw [hsecond _ s hs, hsecond _ s hs]
      simp [sectorParameterEquiv_apply]
    · left
      left
      refine ⟨t, ht, ?_⟩
      simpa [sectorParameterEquiv_apply] using (hsecond (i, true) t ht).symm
  · change ((F i).boundary 2).map t ∈ _
    by_cases ht0 : t = 0
    · subst t
      rw [hfirst i 0 (by simp), zero_mul]
      change H (sectorParameterEquiv 0 i 0) ∈ _
      rw [sectorParameterEquiv_zero]
      exact Or.inl (Or.inl hzero)
    by_cases ht1 : t = 1
    · subst t
      right
      refine ⟨0, by simp, ?_⟩
      simp [hfirst i 1 (by simp), hchord]
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    rcases i with ⟨i, j⟩
    cases i
    · have hpositive : positive = false := by
        cases positive
        · rfl
        · simp at hi
      have hother : occupied (false, !j) := by simp [occupied, hpositive]
      have hne : (false, j) ≠ (false, !j) := by cases j <;> decide
      apply False.elim (hz.1.2 (hshared (false, j) (false, !j) hi hother hne 2 ?_ hti))
      intro s hs
      rw [hfirst _ s hs, hfirst _ s hs]
      simp [sectorParameterEquiv_apply]
    · left
      right
      refine ⟨t, ht, ?_⟩
      simpa [sectorParameterEquiv_apply] using (hfirst (true, j) t ht).symm







theorem m64Intrinsic_residual_core_cap_chord
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : ℝ)
    (F : Bool × Bool → SmoothFace AnnulusCoordinates) (positive : Bool)
    (hsub : ∀ i, (F i).carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsecond : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((F i).boundary 1).map t =
      H (sectorParameterEquiv 0 i (0, t * r)))
    (hfirst : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((F i).boundary 2).map t =
      H (sectorParameterEquiv 0 i (t * r, 0)))
    (hchord : ∀ i t, ((F i).boundary 0).map t =
      (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
        t • H (sectorParameterEquiv 0 i (0, r)))
    (hcoordinates : ∀ i, ∃ (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
      (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates),
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      convexHull ℝ (range b) ⊆ C.source ∧
      (F i).carrier = C '' convexHull ℝ (range b) ∧
      ∀ k, ((F i).boundary k).map = C ∘
        affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)))
    {U K R : Set AnnulusCoordinates}
    (haxes : (fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
      (fun t : ℝ => H (t * r, 0)) '' Icc 0 1 ⊆ K)
    (hremove : (⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      (F i).carrier) ⊆ R)
    (hcover : ∀ p ∈ closure U ∩ K, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ R) :
    ∀ i, (if positive then i = (true, true) else i ≠ (true, true)) →
      closure (U \ R) ∩ (F i).carrier ⊆ ((F i).boundary 0).map '' Icc (0 : ℝ) 1 := by
  have hexposed := m64Intrinsic_retained_cap_exposed_chord H r F positive
    hsub hsecond hfirst hchord hcoordinates
  have havoid := Poincare.Topology.closure_diff_disjoint_of_local_cover hcover
  intro i hi z hz
  have hcap : z ∈ ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      (F i).carrier := mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hz.2⟩⟩
  have hfront := Poincare.Topology.closure_diff_inter_subset_frontier hremove ⟨hz.1, hcap⟩
  exact (hexposed i hi ⟨hfront, hz.2⟩).resolve_left
    (fun hk => disjoint_left.mp havoid hz.1 (haxes hk))

end PoincareConjecture
