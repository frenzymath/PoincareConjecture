import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapInteriorChart
import PoincareConjecture.Proofs.M76.PrimeReduction.FinitePolyhedralIdentityExtension
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartPLTransition
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_supported_polyhedral_motion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {C D : Set V3} {f : V3 → X}
    (hC : IsCompact C) (hf : PolyhedralPLInCharts e f C) (hfi : InjOn f C)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (H : D ≃ₜ D) (hH : H.IsFinitePL) (hDC : D ⊆ interior C)
    (hfix : ∀ x : D, (x : V3) ∈ frontier D → H x = x) :
    ∃ F : X ≃ₜ X,
      (∀ x : D, F (f x) = f (H x)) ∧
      EqOn F id (f '' D)ᶜ ∧
      F '' (f '' D) = f '' D ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 := by
  obtain ⟨Q,hQS,hQT,hQf,hQinv,hQcompat⟩ :=
    exists_original_polyhedral_interior_chart hC hf hfi he
  have hD : IsCompact D := by
    obtain ⟨_,⟨K,hK,hKs,_⟩,_⟩ := hH
    exact hKs ▸ K.isCompact_space_of_finite hK
  let G := H.closedExtension hD.isClosed hfix
  have hGfix : EqOn G id Dᶜ := fun x hx => H.closedExtension_apply_notMem hD.isClosed hfix hx
  have hGPL : G.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 := by
    apply G.toOpenPartialHomeomorph.mem_piecewiseAffineGroupoid_of_local_finitePL
    intro x _
    obtain ⟨K,hK,hxK,_⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
    exact ⟨K.space,hxK (mem_singleton x),hH.closedExtension_finite_on_polyhedron hD.isClosed hfix K hK⟩
  have hDQ : D ⊆ Q.symm.source := hQT.symm.subset.trans' hDC
  obtain ⟨F,hFQ,hFout⟩ := Q.symm.exists_supported_chart_homeomorph G hD hDQ hGfix
  have hforward (i j : ι) :
      (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈ piecewiseAffineGroupoid V3 :=
    Q.symm.supported_chart_transition_mem_piecewiseAffineGroupoid
      (e i).symm (e j).symm G F hD hDQ hGfix hFQ hFout hGPL
      (hQcompat i) (hQcompat j) (he i j)
  have hvalue (x : D) : F (f x) = f (H x) := by
    have hxQ : (x : V3) ∈ Q.target := hDQ x.property
    have hfQ : f x ∈ Q.source := by rw [←hQf]; exact Q.map_target hxQ
    have hval := hFQ hfQ
    change F (f x) = Q.symm (G (Q (f x))) at hval
    rw [hQinv _ (interior_subset (hDC x.property)),
      H.closedExtension_apply_mem hD.isClosed hfix x.property,hQf] at hval
    exact hval
  have hout : EqOn F id (f '' D)ᶜ := by
    have hsame : Q.symm '' D = f '' D := by
      congr 1
      funext x
      exact hQf x
    exact hsame ▸ hFout
  refine ⟨F,hvalue,hout,?_,hforward,?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      rw [hvalue ⟨x,hx⟩]
      exact mem_image_of_mem f (H ⟨x,hx⟩).property
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨f (H.symm ⟨x,hx⟩),mem_image_of_mem f (H.symm ⟨x,hx⟩).property,?_⟩
      rw [hvalue,H.apply_symm_apply]
  · intro i j
    have hinv := (piecewiseAffineGroupoid V3).symm (hforward j i)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using hinv

end PoincareConjecture.M76
