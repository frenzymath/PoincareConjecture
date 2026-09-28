import PoincareConjecture.Proofs.M76.Mathlib.BarycentricMix
import Mathlib.Analysis.Convex.PathConnected











set_option autoImplicit false

open Set StdSimplexCore
open scoped BigOperators

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



theorem single_mem_barycentricFace {s : Finset ι} {i : ι} (hi : i ∈ s) :
    Pi.single i (1 : ℝ) ∈ barycentricFace s := by
  refine ⟨single_mem_stdSimplex ℝ i, ?_⟩
  intro j hj
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  simp [hij]

end StdSimplexCore

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [Fintype ι]



def openVertexStar (A : PreAbstractSimplicialComplex ι) (i : ι) :
    Set A.barycentricSpace := {q | 0 < q.val i}



theorem isOpen_openVertexStar (A : PreAbstractSimplicialComplex ι) (i : ι) :
    IsOpen (A.openVertexStar i) :=
  isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)



theorem exists_mem_openVertexStar (A : PreAbstractSimplicialComplex ι)
    (q : A.barycentricSpace) : ∃ i, q ∈ A.openVertexStar i := by
  obtain ⟨s, _, hqs⟩ := mem_iUnion₂.mp q.property
  by_contra h
  have hnonpos (i : ι) : q.val i ≤ 0 := le_of_not_gt (fun hi => h ⟨i, hi⟩)
  have hsum := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hnonpos i)
  rw [hqs.1.2] at hsum
  norm_num at hsum



theorem mem_face_of_mem_openVertexStar (A : PreAbstractSimplicialComplex ι)
    {q : A.barycentricSpace} {s : Finset ι}
    (hqs : q.val ∈ barycentricFace s) {i : ι} (hi : q ∈ A.openVertexStar i) :
    i ∈ s := by
  by_contra his
  have hpos : 0 < q.val i := hi
  rw [hqs.2 i his] at hpos
  exact lt_irrefl _ hpos




theorem exists_face_containing_openStars (A : PreAbstractSimplicialComplex ι)
    (q : A.barycentricSpace) :
    ∃ s ∈ A.faces, ∀ i, q ∈ A.openVertexStar i → i ∈ s := by
  obtain ⟨s, hs, hqs⟩ := mem_iUnion₂.mp q.property
  exact ⟨s, hs, fun _ hi => A.mem_face_of_mem_openVertexStar hqs hi⟩



def barycentricVertex [DecidableEq ι] (A : PreAbstractSimplicialComplex ι) (i : ι)
    (hi : {i} ∈ A.faces) : A.barycentricSpace :=
  ⟨Pi.single i 1, A.barycentricFace_subset_barycentricSpace hi
    (single_mem_barycentricFace (Finset.mem_singleton_self i))⟩



theorem barycentricVertex_mem_openVertexStar [DecidableEq ι] (A : PreAbstractSimplicialComplex ι)
    (i : ι) (hi : {i} ∈ A.faces) :
    A.barycentricVertex i hi ∈ A.openVertexStar i := by
  simp [barycentricVertex, openVertexStar]





theorem starConvex_openVertexStar_carrier [DecidableEq ι]
    (A : PreAbstractSimplicialComplex ι) (i : ι) :
    StarConvex ℝ (Pi.single i (1 : ℝ))
      (A.barycentricSpace ∩ {q | 0 < q i}) := by
  intro q hq a b ha hb hab
  obtain ⟨s, hs, hqs⟩ := mem_iUnion₂.mp hq.1
  have hi : i ∈ s := A.mem_face_of_mem_openVertexStar (q := ⟨q, hq.1⟩) hqs hq.2
  refine ⟨A.barycentricFace_subset_barycentricSpace hs
    (convex_barycentricFace s (single_mem_barycentricFace hi) hqs ha hb hab), ?_⟩
  change 0 < a * (Pi.single i (1 : ℝ) : ι → ℝ) i + b * q i
  simp only [Pi.single_eq_same, mul_one]
  rcases hb.eq_or_lt with hb0 | hbpos
  · have ha1 : a = 1 := by linarith
    simp [← hb0, ha1]
  · exact add_pos_of_nonneg_of_pos ha (mul_pos hbpos hq.2)



theorem isPathConnected_openVertexStar (A : PreAbstractSimplicialComplex ι)
    (i : ι) (hi : {i} ∈ A.faces) : IsPathConnected (A.openVertexStar i) := by
  classical
  have hcenter : Pi.single i (1 : ℝ) ∈ A.barycentricSpace ∩ {q | 0 < q i} :=
    ⟨(A.barycentricVertex i hi).property, by simp⟩
  have hconn := (A.starConvex_openVertexStar_carrier i).isPathConnected hcenter
  have hpre := hconn.preimage_coe inter_subset_left
  have heq : (Subtype.val : A.barycentricSpace → (ι → ℝ)) ⁻¹'
      (A.barycentricSpace ∩ {q | 0 < q i}) = A.openVertexStar i := by
    ext q
    exact and_iff_right q.property
  rwa [heq] at hpre




theorem openVertexStar_inter_nonempty_of_common_face
    (A : PreAbstractSimplicialComplex ι) {s : Finset ι} (hs : s ∈ A.faces)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    (A.openVertexStar i ∩ A.openVertexStar j).Nonempty := by
  classical
  let q : ι → ℝ := (1 / 2 : ℝ) • Pi.single i 1 + (1 / 2 : ℝ) • Pi.single j 1
  have hq : q ∈ A.barycentricSpace :=
    A.barycentricFace_subset_barycentricSpace hs
      (convex_barycentricFace s (single_mem_barycentricFace hi)
        (single_mem_barycentricFace hj) (by norm_num) (by norm_num) (by norm_num))
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · change 0 < q i
    by_cases hij : i = j
    · subst j
      norm_num [q]
    · simp [q, Ne.symm hij]
  · change 0 < q j
    by_cases hij : i = j
    · subst j
      norm_num [q]
    · simp [q, hij]

end PreAbstractSimplicialComplex
