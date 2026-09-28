import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Perfect

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem RespectsAffineHyperplane.mem_closure_zero_section_sdiff_singleton
    {K : SimplicialComplex ℝ E} {A : E →ᵃ[ℝ] ℝ}
    (halign : K.RespectsAffineHyperplane A)
    (hacc : ∀ p ∈ K.vertices, A p = 0 →
      p ∈ closure ((K.space ∩ {y | A y = 0}) \ {p}))
    {x : E} (hx : x ∈ K.space ∩ {y | A y = 0}) :
    x ∈ closure ((K.space ∩ {y | A y = 0}) \ {x}) := by
  classical
  have hxA : A x = 0 := hx.2
  by_cases hxv : x ∈ K.vertices
  · exact hacc x hxv hxA
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx.1
  have hzeroHull : x ∈ convexHull ℝ ((s : Set E) ∩ {v | A v = 0}) := by
    rcases halign s hs with hneg | hpos
    · have h := s.mem_convexHull_zero_vertices (-A)
        (fun v hv => neg_nonneg.mpr (hneg v (subset_convexHull ℝ _ hv))) hxs
        (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hxA)
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using h
    · exact s.mem_convexHull_zero_vertices A
        (fun v hv => hpos v (subset_convexHull ℝ _ hv)) hxs hxA
  obtain ⟨v, hvs, hvA⟩ := convexHull_nonempty_iff.mp ⟨x, hzeroHull⟩
  have hxne : x ≠ v := by
    intro h
    have hvK : v ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
    exact hxv (h.symm ▸ hvK)
  have hhull : convexHull ℝ ((s : Set E) ∩ {v | A v = 0}) ⊆
      K.space ∩ {y | A y = 0} := by
    intro y hy
    exact ⟨K.convexHull_subset_space hs (convexHull_mono inter_subset_left hy),
      convexHull_min inter_subset_right ((convex_singleton (0 : ℝ)).affine_preimage A) hy⟩
  have hsegment : segment ℝ x v ⊆ K.space ∩ {y | A y = 0} :=
    ((convex_convexHull ℝ _).segment_subset hzeroHull
      (subset_convexHull ℝ _ ⟨hvs, hvA⟩)).trans hhull
  have hnontrivial : (segment ℝ x v).Nontrivial :=
    ⟨x, left_mem_segment ℝ x v, v, right_mem_segment ℝ x v, hxne⟩
  have hpoint := IsPreconnected.preperfect_of_nontrivial hnontrivial
    (convex_segment x v).isPreconnected x (left_mem_segment ℝ x v)
  apply closure_mono _ ((accPt_principal_iff_clusterPt.mp hpoint).mem_closure)
  exact fun y hy => ⟨hsegment hy.1, hy.2⟩

end Geometry.SimplicialComplex
