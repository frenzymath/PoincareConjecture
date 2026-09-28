import PoincareConjecture.Proofs.M76.Mathlib.FiniteSurfaceSectionMarks
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIncidence

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_subordinate_height_section_cut_arcs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices) (c : ℝ)
    {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hsection : P.boundary ℝ = K.space ∩ {x | A x = c})
    {ι : Type*} (U : ι → Set E) (hU : ∀ j, IsOpen (U j))
    (hcover : K.space ∩ {x | A x = c} ⊆ ⋃ j, U j) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)) (t : Fin (N + 3) → ℝ)
      (chart : Fin (N + 3) → ι),
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
      ∀ i j, i ≠ j → Q.cutArc t i ∩ Q.cutArc t j =
        ({Q.edgeCut t i, Q.edgeCut t (finRotate (N + 3) i)} ∩
          {Q.edgeCut t j, Q.edgeCut t (finRotate (N + 3) j)}) := by
  classical
  obtain ⟨N, Q, t, hQ, hQi, hQP, ht, hcuts, hUnion, hchart⟩ :=
    P.exists_subordinate_cut_arcs hP hinj U hU (hsection.subset.trans hcover)
      (K.finite_oneSkeletonHeightSection hK A hA c)
  choose chart hchart using hchart
  have htt (i : Fin (N + 3)) : t i ∈ Ioo (0 : ℝ) 1 := (ht i).1
  have htc (i : Fin (N + 3)) : t i ∈ Icc (0 : ℝ) 1 :=
    ⟨(htt i).1.le, (htt i).2.le⟩
  have hQS := hQP.trans hsection
  have hballs (i : Fin (N + 3)) : IsFinitePLBallPair ℝ (Q.cutArc t i)
      {Q.edgeCut t i, Q.edgeCut t (finRotate (N + 3) i)} :=
    Q.cutArc_ballPair hQ hQi t htt i
  have hmark (i : Fin (N + 3)) :
      Q.edgeCut t i ∈ K.space ∩ {x | A x = c} :=
    hQS.subset (mem_iUnion.mpr ⟨i, Q.edgeCut_mem_edgeSet t (htc i)⟩)
  refine ⟨N, Q, t, chart, hQ, hQi, hQS, htt, hcuts, ?_,
    hUnion.trans hsection, fun i => ⟨hchart i, hballs i⟩, ?_, ?_⟩
  · intro i
    exact K.exists_triangle_intrinsicInterior_of_notMem_oneSkeletonHeightSection
      hpure A (hmark i) (ht i).2
  · intro i
    have hleft : Q.edgeCut t i ∈ Q.cutArc t i :=
      (hballs i).1 (by simp)
    have hright : Q.edgeCut t i ∈ Q.cutArc t ((finRotate (N + 3)).symm i) := by
      apply (hballs ((finRotate (N + 3)).symm i)).1
      simp only [Equiv.apply_symm_apply, mem_insert_iff, mem_singleton_iff, or_true]
    exact ⟨hchart i hleft, hchart _ hright⟩
  · intro i j hij
    exact Q.cutArc_inter_of_ne hQ hQi t htt hij

end Geometry.SimplicialComplex
