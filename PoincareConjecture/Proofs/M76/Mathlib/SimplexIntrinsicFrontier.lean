import PoincareConjecture.Proofs.M76.Mathlib.AffineIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricRealization
import PoincareConjecture.Proofs.M76.Mathlib.StdSimplexCoreBoundary









set_option autoImplicit false

open Set

namespace StdSimplexCore

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem injOn_barycentricMap_affineSpan (v : ι → E) (hv : AffineIndependent ℝ v) :
    InjOn (barycentricMap v) (affineSpan ℝ (stdSimplex ℝ ι)) := by
  intro q hq r hr he
  have hqsum := sum_eq_one_of_mem_affineSpan_stdSimplexCore (η := 0) hq
  have hrsum := sum_eq_one_of_mem_affineSpan_stdSimplexCore (η := 0) hr
  funext i
  exact hv.eq_of_sum_eq_sum (hqsum.trans hrsum.symm)
    (by simpa only [barycentricMap_apply] using he) i (Finset.mem_univ i)

variable [Nonempty ι]

omit [Fintype ι] in



theorem intrinsicFrontier_convexHull_range [Finite ι] (v : ι → E)
    (hv : AffineIndependent ℝ v) :
    intrinsicFrontier ℝ (convexHull ℝ (range v)) =
      ⋃ i : ι, convexHull ℝ (v '' {j | j ≠ i}) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have himage : barycentricMap v '' stdSimplex ℝ ι = convexHull ℝ (range v) := by
    simpa [barycentricFace] using image_barycentricFace v Finset.univ
  have hfront := (barycentricMap v).toLinearMap.toAffineMap.intrinsicFrontier_image_of_injOn
    (stdSimplex ℝ ι) (injOn_barycentricMap_affineSpan v hv)
  change intrinsicFrontier ℝ (barycentricMap v '' stdSimplex ℝ ι) =
    barycentricMap v '' intrinsicFrontier ℝ (stdSimplex ℝ ι) at hfront
  rw [himage] at hfront
  rw [hfront]
  have hbound : (Fintype.card ι : ℝ) * 0 < 1 := by simp
  have herase (i : ι) : ((Finset.univ.erase i : Finset ι) : Set ι) = {j | j ≠ i} := by
    ext j
    simp
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hqs, i, hi⟩ := (mem_intrinsicFrontier_stdSimplexCore_iff hbound).mp hq
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hqface : q ∈ barycentricFace (Finset.univ.erase i) := by
      refine ⟨hqs, fun j hj => ?_⟩
      have hji : j = i := by simpa using hj
      simpa only [hji] using hi
    have h := mem_image_of_mem (barycentricMap v) hqface
    rw [image_barycentricFace] at h
    simpa only [herase] using h
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hi' : x ∈ barycentricMap v '' barycentricFace (Finset.univ.erase i) := by
      rw [image_barycentricFace]
      simpa only [herase] using hi
    obtain ⟨q, hq, rfl⟩ := hi'
    refine ⟨q, (mem_intrinsicFrontier_stdSimplexCore_iff hbound).mpr ?_, rfl⟩
    exact ⟨hq.1, i, hq.2 i (Finset.notMem_erase i Finset.univ)⟩

end StdSimplexCore

namespace AffineIndependent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]




theorem mem_intrinsicFrontier_convexHull_finset {s : Finset E} (hs : s.Nonempty)
    (hv : AffineIndependent ℝ ((↑) : s → E)) (x : E) :
    x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ↔
      ∃ i ∈ s, x ∈ convexHull ℝ ((s.erase i : Finset E) : Set E) := by
  let : Nonempty s := hs.to_subtype
  have he (i : s) : ((↑) : s → E) '' {j | j ≠ i} = (s.erase i : Set E) := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩
    · intro hy
      obtain ⟨hyi, hys⟩ := Finset.mem_erase.mp hy
      exact ⟨⟨y, hys⟩, fun h => hyi (congrArg Subtype.val h), rfl⟩
  have hfront := StdSimplexCore.intrinsicFrontier_convexHull_range ((↑) : s → E) hv
  have hrange : range ((↑) : s → E) = (s : Set E) := by ext; simp
  rw [hrange] at hfront
  simp only [he] at hfront
  rw [hfront, mem_iUnion]
  simp only [Subtype.exists, exists_prop]

omit [DecidableEq E] in



theorem convexHull_subset_intrinsicFrontier {s t : Finset E}
    (hv : AffineIndependent ℝ ((↑) : s → E)) (ht : t ⊂ s) :
    convexHull ℝ (t : Set E) ⊆ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨i, hi, hit⟩ := Finset.exists_of_ssubset ht
  intro x hx
  apply (mem_intrinsicFrontier_convexHull_finset ⟨i, hi⟩ hv x).mpr
  refine ⟨i, hi, convexHull_mono ?_ hx⟩
  intro y hy
  exact Finset.mem_erase.mpr ⟨fun h => hit (h ▸ hy), ht.subset hy⟩

end AffineIndependent
