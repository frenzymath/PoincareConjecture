import PoincareConjecture.Proofs.M76.Mathlib.ZeroChargeLocalSection
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]





theorem link_zero_eq_empty_of_isolated_section
    (K : SimplicialComplex ℝ E) (L : E →ₗ[ℝ] ℝ)
    (hlocal : ∀ᶠ x in 𝓝 (0 : E), x ∈ K.space ∩ {y | L y = 0} → x = 0) :
    (K.link 0).space ∩ {x | L x = 0} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨r, hr, hnear⟩ := Set.exists_pos_smul_mem_of_mem_nhds hlocal y
  have hy0 : y ≠ 0 := fun h => K.zero_notMem_link_space (h ▸ hy.1)
  have hry : r • y ∈ K.space := by
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy.1
    apply K.convexHull_subset_space hs.2.2
    exact (convex_convexHull ℝ _).smul_mem_of_zero_mem
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))
      (convexHull_mono (Finset.subset_insert _ _) hys) ⟨hr.1.le, hr.2⟩
  exact smul_ne_zero hr.1.ne' hy0 (hnear ⟨hry, by
    change L (r • y) = 0
    rw [map_smul, hy.2, smul_zero]⟩)





theorem ncard_link_zero_eq_two_of_zero_charge_nonisolated
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    (h : HasAlexanderCurvePresentation (K.space ∩ {x | L x = 0}) 0)
    (hacc : (0 : E) ∈ closure ((K.space ∩ {x | L x = 0}) \ {0})) :
    ((K.link 0).space ∩ {x | L x = 0}).ncard = 2 := by
  have hq : (0 : E) ∈ K.space ∩ {x | L x = 0} :=
    ⟨K.vertices_subset_space hzero, L.map_zero⟩
  obtain ⟨u, v, hu, hv, hinter, _, hlocal⟩ := h.exists_local_segments_of_nonisolated hq hacc
  exact K.ncard_link_zero_of_local_segments hK hzero L hu hv hinter.subset hlocal





theorem ncard_link_zero_eq_zero_or_two_of_zero_charge
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    (h : HasAlexanderCurvePresentation (K.space ∩ {x | L x = 0}) 0) :
    ((K.link 0).space ∩ {x | L x = 0}).ncard = 0 ∨
      ((K.link 0).space ∩ {x | L x = 0}).ncard = 2 := by
  have hq : (0 : E) ∈ K.space ∩ {x | L x = 0} :=
    ⟨K.vertices_subset_space hzero, L.map_zero⟩
  rcases h.local_germ_alternatives hq with hisolated | hsegments
  · left
    have hempty := K.link_zero_eq_empty_of_isolated_section L
      (hisolated.mono fun _ hx => hx.mp)
    rw [hempty, ncard_empty]
  · obtain ⟨u, v, hu, hv, hinter, _, hlocal⟩ := hsegments
    exact Or.inr (K.ncard_link_zero_of_local_segments hK hzero L hu hv hinter.subset hlocal)

end Geometry.SimplicialComplex
