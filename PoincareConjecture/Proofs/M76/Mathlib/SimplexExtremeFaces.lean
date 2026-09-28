import PoincareConjecture.Proofs.M76.Mathlib.AffineInterpolation
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.SimplicialComplex.Basic










set_option autoImplicit false

open Set

variable {E : Type*}



theorem IsExtreme.inter_set [AddCommGroup E] [Module ℝ E]
    {s t : Set E} (h : IsExtreme ℝ s t) (r : Set E) :
    IsExtreme ℝ (s ∩ r) (t ∩ r) := by
  refine ⟨inter_subset_inter_left _ h.subset, ?_⟩
  intro x hx y hy z hz hseg
  exact ⟨h.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 hseg, hx.2⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem AffineIndependent.isExtreme_convexHull_finset_subset [FiniteDimensional ℝ E]
    {s t : Finset E} (hs : AffineIndependent ℝ (fun x : (s : Set E) => (x : E)))
    (hts : t ⊆ s) :
    IsExtreme ℝ (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨a, ha⟩ := hs.exists_continuousAffineMap_eqOn
    (fun v => if v ∈ t then (0 : ℝ) else 1)
  have hn : convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ a x} := by
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage a.toAffineMap)
    intro v hv
    change 0 ≤ a v
    rw [ha hv]
    dsimp only
    split_ifs <;> norm_num
  have hzvertices : (s : Set E) ∩ {v | a v = 0} = (t : Set E) := by
    ext v
    constructor
    · rintro ⟨hvs, hv0⟩
      by_contra hvt
      change v ∉ t at hvt
      change a v = 0 at hv0
      simp only [ha hvs, if_neg hvt, one_ne_zero] at hv0
    · intro hvt
      change v ∈ t at hvt
      refine ⟨hts hvt, ?_⟩
      change a v = 0
      simp only [ha (hts hvt), if_pos hvt]
  have hz : convexHull ℝ (t : Set E) ⊆ {x | a x = 0} := by
    apply convexHull_min _ ((convex_singleton (0 : ℝ)).affine_preimage a.toAffineMap)
    intro v hv
    exact (hzvertices.symm ▸ hv).2
  refine ⟨convexHull_mono hts, ?_⟩
  intro x hx y hy z hzt hseg
  have hx0 : 0 ≤ a x := hn hx
  have hy0 : 0 ≤ a y := hn hy
  have hz0 := hz hzt
  rw [openSegment_eq_image_lineMap] at hseg
  obtain ⟨r, hr, rfl⟩ := hseg
  change a.toAffineMap (AffineMap.lineMap x y r) = 0 at hz0
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring'] at hz0
  change r * (a y - a x) + a x = 0 at hz0
  have hAx : a x = 0 := by
    have hmul := mul_nonneg hr.1.le hy0
    nlinarith [hr.2]
  have hxf := s.mem_convexHull_zero_vertices a.toAffineMap
    (fun v hv => hn (subset_convexHull ℝ _ hv)) hx hAx
  change x ∈ convexHull ℝ ((s : Set E) ∩ {v | a v = 0}) at hxf
  rwa [hzvertices] at hxf

namespace Geometry.SimplicialComplex




theorem isExtreme_convexHull_section_inter [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (r : Set E) :
    IsExtreme ℝ (convexHull ℝ (s : Set E) ∩ r)
      ((convexHull ℝ (s : Set E) ∩ r) ∩ (convexHull ℝ (t : Set E) ∩ r)) := by
  classical
  have hext := ((K.indep hs).isExtreme_convexHull_finset_subset
    (t := s ∩ t) Finset.inter_subset_left).inter_set r
  have heq : convexHull ℝ ((s ∩ t : Finset E) : Set E) ∩ r =
      (convexHull ℝ (s : Set E) ∩ r) ∩ (convexHull ℝ (t : Set E) ∩ r) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    ext x
    simp only [mem_inter_iff]
    tauto
  exact heq ▸ hext

end Geometry.SimplicialComplex
