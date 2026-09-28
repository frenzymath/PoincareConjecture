import PoincareConjecture.Proofs.M76.Mathlib.SurfaceSectionCutArcs
import PoincareConjecture.Proofs.M76.Mathlib.TriangleInteriorHeightBox
import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap
import Mathlib.Topology.Separation.Hausdorff












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_disjoint_affine_height_boxes_at_marks
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices) (c : ℝ)
    {ι : Type*} [Finite ι] (p : ι → E) (hinj : Function.Injective p)
    (hheight : ∀ i, A (p i) = c)
    (hmark : ∀ i, ∃ s ∈ K.faces, s.card = 3 ∧
      p i ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (W : ι → Set E) (hW : ∀ i, IsOpen (W i)) (hpW : ∀ i, p i ∈ W i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (f : ι → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E),
      r ∈ Ioo 0 ε ∧
      (∀ i, f i 0 = p i ∧ f i '' box r ⊆ W i ∧
        p i ∈ interior (f i '' box r) ∧
        (∀ x, A (f i x) = c + x.1.1) ∧
        ∀ x ∈ box r, f i x ∈ K.space ↔ x.2 = 0) ∧
      Pairwise fun i j => Disjoint (f i '' box r) (f j '' box r) := by
  classical
  obtain ⟨V, hV, hVdisj⟩ := (finite_range p).t2_separation
  have hlocal (i : ι) :
      ∃ (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (r : ℝ),
        0 < r ∧ f 0 = p i ∧ f '' box r ⊆ V (p i) ∩ W i ∧
        p i ∈ interior (f '' box r) ∧
        (∀ x, A (f x) = c + x.1.1) ∧
        ∀ x ∈ box r, f x ∈ K.space ↔ x.2 = 0 := by
    obtain ⟨s, hs, hsc, hps⟩ := hmark i
    simpa only [hheight i] using
      K.exists_triangle_interior_affine_height_box hK hbound hdim hs hsc A hA hps
        ((hV (p i)).2.inter (hW i)) ⟨(hV (p i)).1, hpW i⟩
  choose f r hr hf0 hfsub _ hfheight hfcarrier using hlocal
  obtain ⟨δ, hδ, hδr⟩ :=
    (Set.toFinite (univ : Set ι)).exists_pos_lt_positive_values r hε
  have hsmall (i : ι) : box δ ⊆ box (r i) := by
    rw [box_eq_closedBall, box_eq_closedBall]
    exact Metric.closedBall_subset_closedBall (hδr i (mem_univ i) (hr i)).le
  have hfsmall (i : ι) : f i '' box δ ⊆ V (p i) ∩ W i :=
    (image_mono (hsmall i)).trans (hfsub i)
  refine ⟨δ, f, hδ, ?_, ?_⟩
  · intro i
    refine ⟨hf0 i, (hfsmall i).trans inter_subset_right, ?_, hfheight i,
      fun x hx => hfcarrier i x (hsmall i hx)⟩
    change p i ∈ interior ((f i).toHomeomorph '' box δ)
    rw [← (f i).toHomeomorph.image_interior]
    exact ⟨0, zero_mem_interior_box hδ.1, hf0 i⟩
  · intro i j hij
    exact (hVdisj (mem_range_self i) (mem_range_self j)
      (fun h => hij (hinj h))).mono
        ((hfsmall i).trans inter_subset_left) ((hfsmall j).trans inter_subset_left)







theorem exists_subordinate_height_section_cut_boxes
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hdim : Module.finrank ℝ E = 3)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices) (c : ℝ)
    {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hsection : P.boundary ℝ = K.space ∩ {x | A x = c})
    {ι : Type*} (U : ι → Set E) (hU : ∀ j, IsOpen (U j))
    (hcover : K.space ∩ {x | A x = c} ⊆ ⋃ j, U j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)) (t : Fin (N + 3) → ℝ)
      (chart : Fin (N + 3) → ι) (r : ℝ)
      (f : Fin (N + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E),
      Q.HasSimplicialEdges ∧ Function.Injective Q ∧
      Q.boundary ℝ = K.space ∩ {x | A x = c} ∧
      (∀ i, t i ∈ Ioo (0 : ℝ) 1) ∧ Function.Injective (Q.edgeCut t) ∧
      (∀ i, ∃ s ∈ K.faces, s.card = 3 ∧
        Q.edgeCut t i ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) ∧
      (⋃ i, Q.cutArc t i) = K.space ∩ {x | A x = c} ∧
      (∀ i, Q.cutArc t i ⊆ U (chart i) ∧
        IsFinitePLBallPair ℝ (Q.cutArc t i)
          {Q.edgeCut t i, Q.edgeCut t (finRotate (N + 3) i)}) ∧
      (∀ i, Q.edgeCut t i ∈ U (chart i) ∩
        U (chart ((finRotate (N + 3)).symm i))) ∧
      (∀ i j, i ≠ j → Q.cutArc t i ∩ Q.cutArc t j =
        ({Q.edgeCut t i, Q.edgeCut t (finRotate (N + 3) i)} ∩
          {Q.edgeCut t j, Q.edgeCut t (finRotate (N + 3) j)})) ∧
      r ∈ Ioo 0 ε ∧
      (∀ i, f i 0 = Q.edgeCut t i ∧
        f i '' box r ⊆ U (chart i) ∩ U (chart ((finRotate (N + 3)).symm i)) ∧
        Q.edgeCut t i ∈ interior (f i '' box r) ∧
        (∀ x, A (f i x) = c + x.1.1) ∧
        ∀ x ∈ box r, f i x ∈ K.space ↔ x.2 = 0) ∧
      Pairwise fun i j => Disjoint (f i '' box r) (f j '' box r) := by
  classical
  obtain ⟨N, Q, t, chart, hQ, hQi, hQS, ht, hcuts, hmarks, hUnion, harcs,
    hadjacent, hinter⟩ :=
    K.exists_subordinate_height_section_cut_arcs hK hpure A hA c P hP hinj
      hsection U hU hcover
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, htc, hst⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq htc
  have hheight (i : Fin (N + 3)) : A (Q.edgeCut t i) = c := by
    have hx : Q.edgeCut t i ∈ K.space ∩ {x | A x = c} :=
      hQS.subset (mem_iUnion.mpr ⟨i, Q.edgeCut_mem_edgeSet t
        ⟨(ht i).1.le, (ht i).2.le⟩⟩)
    exact hx.2
  obtain ⟨r, f, hr, hf, hdisj⟩ :=
    K.exists_disjoint_affine_height_boxes_at_marks hK hbound hdim A hA c
      (Q.edgeCut t) hcuts hheight hmarks
      (fun i => U (chart i) ∩ U (chart ((finRotate (N + 3)).symm i)))
      (fun i => (hU (chart i)).inter (hU _)) hadjacent hε
  exact ⟨N, Q, t, chart, r, f, hQ, hQi, hQS, ht, hcuts, hmarks, hUnion,
    harcs, hadjacent, hinter, hr, hf, hdisj⟩

end Geometry.SimplicialComplex
