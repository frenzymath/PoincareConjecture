import PoincareConjecture.Proofs.M76.Mathlib.CoreProjectionCoordinates
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic










set_option autoImplicit false

open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



noncomputable def faceInclusion (s : Finset ι) : (s → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => if hi : i ∈ s then
    ContinuousLinearMap.proj ⟨i, hi⟩ else 0)

omit [Fintype ι] in


theorem faceInclusion_apply_mem (s : Finset ι) (q : s → ℝ) {i : ι} (hi : i ∈ s) :
    faceInclusion s q i = q ⟨i, hi⟩ := by
  simp only [faceInclusion, ContinuousLinearMap.pi_apply, dif_pos hi,
    ContinuousLinearMap.proj_apply]

omit [Fintype ι] in


theorem faceInclusion_apply_notMem (s : Finset ι) (q : s → ℝ) {i : ι} (hi : i ∉ s) :
    faceInclusion s q i = 0 := by
  simp only [faceInclusion, ContinuousLinearMap.pi_apply, dif_neg hi,
    zero_apply]



theorem sum_faceInclusion (s : Finset ι) (q : s → ℝ) :
    ∑ i, faceInclusion s q i = ∑ i, q i := by
  have he : (∑ i, faceInclusion s q i) = ∑ i ∈ s, faceInclusion s q i := by
    symm
    apply Fintype.sum_subset
    intro i hi
    by_contra his
    exact hi (faceInclusion_apply_notMem s q his)
  rw [he, ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl (fun i _ => faceInclusion_apply_mem s q i.property)



def barycentricFace (s : Finset ι) : Set (ι → ℝ) :=
  {q | q ∈ stdSimplex ℝ ι ∧ ∀ i ∉ s, q i = 0}

omit [DecidableEq ι] in


theorem isClosed_barycentricFace (s : Finset ι) : IsClosed (barycentricFace s) := by
  have he : barycentricFace s = stdSimplex ℝ ι ∩
      ⋂ i ∉ s, {q : ι → ℝ | q i = 0} := by
    ext q
    simp only [barycentricFace, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [he]
  exact (isClosed_stdSimplex ℝ ι).inter (isClosed_iInter fun i =>
    isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const)

omit [DecidableEq ι] in


theorem isCompact_barycentricFace (s : Finset ι) : IsCompact (barycentricFace s) :=
  (isCompact_stdSimplex ℝ ι).of_isClosed_subset (isClosed_barycentricFace s) (fun _ h => h.1)



theorem faceInclusion_mem_barycentricFace (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    {q : s → ℝ} (hq : q ∈ stdSimplexCore s η) : faceInclusion s q ∈ barycentricFace s := by
  refine ⟨⟨fun i => ?_, (sum_faceInclusion s q).trans hq.2⟩,
    fun i hi => faceInclusion_apply_notMem s q hi⟩
  by_cases hi : i ∈ s
  · rw [faceInclusion_apply_mem s q hi]
    exact hη.trans (hq.1 ⟨i, hi⟩)
  · rw [faceInclusion_apply_notMem s q hi]



theorem faceInclusion_mem_faceRegion (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    {q : s → ℝ} (hq : q ∈ stdSimplexCore s η) : faceInclusion s q ∈ faceRegion s η := by
  refine ⟨(faceInclusion_mem_barycentricFace s hη hq).1, ?_, ?_⟩
  · intro i hi
    rw [faceInclusion_apply_mem s q hi]
    exact hq.1 ⟨i, hi⟩
  · intro i hi
    simpa only [faceInclusion_apply_notMem s q hi] using hη



theorem projectToFace_mem_barycentricFace (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ}
    (hq : q ∈ faceRegion s η) : projectToFace s η q ∈ barycentricFace s := by
  refine ⟨projectToFace_mem_stdSimplex s hη hbound ⟨q, hq⟩, ?_⟩
  intro i hi
  simp only [projectToFace, if_neg hi]

omit [Fintype ι] in


theorem faceInclusion_projectToFace (s : Finset ι) (η : ℝ) (q : ι → ℝ) :
    faceInclusion s (fun i : s => projectToFace s η q i) = projectToFace s η q := by
  ext i
  by_cases hi : i ∈ s
  · exact faceInclusion_apply_mem s _ hi
  · simp only [faceInclusion_apply_notMem s _ hi, projectToFace, if_neg hi]

omit [DecidableEq ι] in


theorem subset_of_mem_barycentricFace_faceRegion {s t : Finset ι} {η : ℝ} (hη : 0 < η)
    {q : ι → ℝ} (hqt : q ∈ barycentricFace t) (hqs : q ∈ faceRegion s η) : s ⊆ t := by
  intro i hi
  by_contra hit
  have h := hqs.2.1 i hi
  rw [hqt.2 i hit] at h
  exact hη.not_ge h

end StdSimplexCore

namespace PreAbstractSimplicialComplex

open StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



def barycentricSpace (A : PreAbstractSimplicialComplex ι) : Set (ι → ℝ) :=
  ⋃ s ∈ A.faces, barycentricFace s

omit [DecidableEq ι] in


theorem isCompact_barycentricSpace (A : PreAbstractSimplicialComplex ι) :
    IsCompact A.barycentricSpace :=
  (Set.toFinite A.faces).isCompact_biUnion (fun s _ => isCompact_barycentricFace s)

omit [DecidableEq ι] in


theorem barycentricFace_subset_barycentricSpace (A : PreAbstractSimplicialComplex ι)
    {s : Finset ι} (hs : s ∈ A.faces) : barycentricFace s ⊆ A.barycentricSpace :=
  subset_iUnion₂_of_subset s hs Subset.rfl



def coreRegion (A : PreAbstractSimplicialComplex ι) (s : Finset ι) (η : ℝ) : Set (ι → ℝ) :=
  A.barycentricSpace ∩ faceRegion s η

omit [DecidableEq ι] in


theorem isCompact_coreRegion (A : PreAbstractSimplicialComplex ι) (s : Finset ι) (η : ℝ) :
    IsCompact (A.coreRegion s η) :=
  A.isCompact_barycentricSpace.inter_right (isClosed_faceRegion s η)



theorem projectToFace_mem_coreRegion (A : PreAbstractSimplicialComplex ι)
    {s : Finset ι} (hs : s ∈ A.faces) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ}
    (hq : q ∈ faceRegion s η) : projectToFace s η q ∈ A.coreRegion s η := by
  refine ⟨A.barycentricFace_subset_barycentricSpace hs
    (projectToFace_mem_barycentricFace s hη hbound hq), ?_⟩
  rw [← faceInclusion_projectToFace s η q]
  exact faceInclusion_mem_faceRegion s hη (projectToFace_mem_core s hη hbound ⟨q, hq⟩)

omit [DecidableEq ι] in


theorem exists_mem_coreRegion (A : PreAbstractSimplicialComplex ι)
    {η : ℝ} (hη : 0 < η) (hbound : (Fintype.card ι : ℝ) * η < 1)
    {q : ι → ℝ} (hq : q ∈ A.barycentricSpace) :
    ∃ s ∈ A.faces, q ∈ A.coreRegion s η := by
  classical
  obtain ⟨t, ht, hqt⟩ := mem_iUnion₂.mp hq
  obtain ⟨s, hs, _, hqs⟩ := exists_mem_faceRegion hη.le hbound hqt.1
  have hst := subset_of_mem_barycentricFace_faceRegion hη hqt hqs
  exact ⟨s, (A.isRelLowerSet_faces ht).2 hst hs, hq, hqs⟩

end PreAbstractSimplicialComplex
