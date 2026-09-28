import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteCutPLDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3ComponentReassembly
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem PLDomain.extension_of_local_collar_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R C O : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hC : IsCompact C) (hCR : C ⊆ R)
    (hO : IsOpen O) (hOC : closure O ⊆ interior C) (hcut : PLDomain e (C \ O)) :
    PLDomain e (R \ O) := by
  have hOR : closure O ⊆ interior R := hOC.trans (interior_mono hCR)
  obtain ⟨hcompact,_,hfront,_⟩ := compact_collar_cut_geometry hR hO hOR
  have hfrontC := (compact_collar_cut_geometry hC hO hOC).2.2.1
  refine ⟨he.cover,he.compatible,hcompact.isClosed,?_⟩
  intro x hx
  rcases hfront.subset hx with hxR | hxO
  · obtain ⟨ell,v,H,hv,hxH,hzero,hcompat,hhalf⟩ := he.halfspace x hxR
    have hxoff : x ∈ (closure O)ᶜ := fun h => hxR.2 (hOR h)
    refine ⟨ell,v,H.restrOpen (closure O)ᶜ isClosed_closure.isOpen_compl,
      hv,⟨hxH,hxoff⟩,hzero,?_,?_⟩
    · intro j
      exact (e j).piecewiseAffine_compatible_restrOpen_right H (hcompat j)
        isClosed_closure.isOpen_compl
    · intro y hy
      change y ∈ R \ O ↔ 0 ≤ ell (H y)
      exact ⟨fun h => (hhalf y hy.1).mp h.1,
        fun h => ⟨(hhalf y hy.1).mpr h,fun hyO => hy.2 (subset_closure hyO)⟩⟩
  · have hxCcut : x ∈ frontier (C \ O) := hfrontC.symm.subset (Or.inr hxO)
    obtain ⟨ell,v,H,hv,hxH,hzero,hcompat,hhalf⟩ := hcut.halfspace x hxCcut
    refine ⟨ell,v,H.restrOpen (interior C) isOpen_interior,
      hv,⟨hxH,hOC (frontier_subset_closure hxO)⟩,hzero,?_,?_⟩
    · intro j
      exact (e j).piecewiseAffine_compatible_restrOpen_right H (hcompat j) isOpen_interior
    · intro y hy
      change y ∈ R \ O ↔ 0 ≤ ell (H y)
      exact ⟨fun h => (hhalf y hy.1).mp ⟨interior_subset hy.2,h.2⟩,
        fun h => ⟨hCR (interior_subset hy.2),((hhalf y hy.1).mpr h).2⟩⟩

theorem local_collar_frontier_eq_spherical_subfamily
    {X ι ν : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {C O : Set X}
    (hC : IsCompact C) (hO : IsOpen O) (hOC : closure O ⊆ interior C)
    (D : ν → Set X) (sD : ∀ j, ChartwisePLSphere e (D j))
    (hfront : frontier (C \ O) = ⋃ j, D j) :
    frontier O = ⋃ j : {j // D j ⊆ frontier O}, D j.val := by
  have hdecomp := (compact_collar_cut_geometry hC hO hOC).2.2.1
  have hdis : Disjoint (frontier C) (frontier O) := by
    exact disjoint_left.mpr (fun _ hxC hxO => hxC.2 (hOC (frontier_subset_closure hxO)))
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp
      (hfront.subset (hdecomp.symm.subset (Or.inr hx)))
    have hDj : D j ⊆ frontier C ∪ frontier O :=
      (subset_iUnion D j).trans (hfront.symm.subset.trans hdecomp.subset)
    have hsub : D j ⊆ frontier O := by
      intro y hy
      rcases hDj hy with hyC | hyO
      · obtain ⟨z,_,hzC,hzO⟩ := isPreconnected_closed_iff.mp (sD j).isConnected.isPreconnected
          (frontier C) (frontier O) isClosed_frontier isClosed_frontier hDj
          ⟨y,hy,hyC⟩ ⟨x,hj,hx⟩
        exact False.elim (disjoint_left.mp hdis hzC hzO)
      · exact hyO
    exact mem_iUnion.mpr ⟨⟨j,hsub⟩,hj⟩
  · exact iUnion_subset (fun j => j.property)

end PoincareConjecture.M76
