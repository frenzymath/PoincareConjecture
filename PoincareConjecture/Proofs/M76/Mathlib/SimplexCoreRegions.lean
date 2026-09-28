import PoincareConjecture.Proofs.M76.Mathlib.SimplexCoreBoxCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.StdSimplexCoreBoundary











set_option autoImplicit false

open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι]




def faceRegion (s : Finset ι) (η : ℝ) : Set (ι → ℝ) :=
  {q | q ∈ stdSimplex ℝ ι ∧ (∀ i ∈ s, η ≤ q i) ∧ ∀ i ∉ s, q i ≤ η}



theorem isClosed_faceRegion (s : Finset ι) (η : ℝ) : IsClosed (faceRegion s η) := by
  have he : faceRegion s η = stdSimplex ℝ ι ∩
      (⋂ i ∈ s, {q : ι → ℝ | η ≤ q i}) ∩ (⋂ i ∉ s, {q : ι → ℝ | q i ≤ η}) := by
    ext q
    simp only [faceRegion, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_assoc]
  rw [he]
  exact ((isClosed_stdSimplex ℝ ι).inter (isClosed_iInter fun i =>
    isClosed_iInter fun _ => isClosed_le continuous_const (continuous_apply i))).inter
      (isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_le (continuous_apply i) continuous_const)



theorem isCompact_faceRegion (s : Finset ι) (η : ℝ) : IsCompact (faceRegion s η) :=
  (isCompact_stdSimplex ℝ ι).of_isClosed_subset (isClosed_faceRegion s η) (fun _ h => h.1)




theorem exists_mem_faceRegion {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) :
    ∃ s : Finset ι, s.Nonempty ∧ (∀ i ∈ s, 0 < q i) ∧ q ∈ faceRegion s η := by
  classical
  let s := Finset.univ.filter (fun i => η < q i)
  have hs : s.Nonempty := by
    by_contra hn
    have hle : ∀ i, q i ≤ η := by
      intro i
      by_contra hi
      exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_of_not_ge hi⟩⟩
    have hsum : (∑ i, q i) ≤ (Fintype.card ι : ℝ) * η := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hle i)
    linarith [hq.2]
  refine ⟨s, hs, ?_, hq, ?_, ?_⟩
  · intro i hi
    exact hη.trans_lt (Finset.mem_filter.mp hi).2
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.le
  · intro i hi
    exact le_of_not_gt (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))




theorem coordinate_eq_of_mem_faceRegions {s t : Finset ι} {η : ℝ} {q : ι → ℝ}
    (hs : q ∈ faceRegion s η) (ht : q ∈ faceRegion t η)
    {i : ι} (hi : i ∈ s) (hit : i ∉ t) : q i = η :=
  le_antisymm (ht.2.2 i hit) (hs.2.1 i hi)




theorem exists_threshold_of_mem_faceRegions {s t : Finset ι} {η : ℝ} {q : ι → ℝ}
    (hs : q ∈ faceRegion s η) (ht : q ∈ faceRegion t η)
    (hne : s ≠ t) (hcard : t.card ≤ s.card) : ∃ i ∈ s, i ∉ t ∧ q i = η := by
  have hnot : ¬s ⊆ t := fun h => hne (Finset.eq_of_subset_of_card_le h hcard)
  obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp hnot
  exact ⟨i, hi, hit, coordinate_eq_of_mem_faceRegions hs ht hi hit⟩

variable [DecidableEq ι]




noncomputable def faceRegionBoxHomeomorph (s : Finset ι) {η : ℝ} (hη : 0 ≤ η) :
    faceRegion s η ≃ₜ boxRegion s {i // i ∉ s} η := by
  classical
  let e := Homeomorph.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ => ℝ)
  apply e.subtype
  intro q
  change q ∈ faceRegion s η ↔
    (∀ i : s, η ≤ q i) ∧ (fun i : {i // i ∉ s} => q i) ∈ Icc 0 (fun _ => η) ∧
      (∑ i : s, q i) + ∑ i : {i // i ∉ s}, q i = 1
  have hsum : (∑ i : s, q i) + ∑ i : {i // i ∉ s}, q i = ∑ i, q i := by
    convert Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) q using 1
    congr 1
    congr 1
    ext i
    simp
  rw [hsum]
  constructor
  · intro hq
    exact ⟨fun i => hq.2.1 i i.property,
      ⟨fun i => hq.1.1 i, fun i => hq.2.2 i i.property⟩, hq.1.2⟩
  · rintro ⟨hi, hv, hsum⟩
    refine ⟨⟨fun i => ?_, hsum⟩, fun i his => hi ⟨i, his⟩, fun i his => hv.2 ⟨i, his⟩⟩
    by_cases his : i ∈ s
    · exact hη.trans (hi ⟨i, his⟩)
    · exact hv.1 ⟨i, his⟩



noncomputable def faceRegionProductHomeomorph (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) :
    (stdSimplexCore s η × Icc (0 : {i // i ∉ s} → ℝ) (fun _ => η)) ≃ₜ faceRegion s η := by
  classical
  have hc : (Fintype.card s : ℝ) + Fintype.card {i // i ∉ s} = Fintype.card ι := by
    simpa using Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) (fun _ => (1 : ℝ))
  exact (boxHomeomorph hη (hc ▸ hbound)).trans (faceRegionBoxHomeomorph s hη).symm

end StdSimplexCore
