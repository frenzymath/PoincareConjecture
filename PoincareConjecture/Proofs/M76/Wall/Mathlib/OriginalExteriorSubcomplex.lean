import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClosedComplementSubcomplex
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {X : Type*} [TopologicalSpace X]

private theorem closure_complement_inside {C L : Set X}
    (hC : IsClosed C) (hLC : L ⊆ interior C) :
    closure (C \ L) = C \ interior L := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨closure_minimal sdiff_subset hC hx, ?_⟩
    have houtside : closure (C \ L) ⊆ closure Lᶜ :=
      closure_mono (fun _ hy => hy.2)
    have hxoutside := houtside hx
    simpa only [closure_compl, mem_compl_iff] using hxoutside
  · rintro x ⟨hxC, hxL⟩
    by_cases hxl : x ∈ L
    · have hxc : x ∈ closure Lᶜ := by
        simpa only [closure_compl, mem_compl_iff] using hxL
      have hsub : interior C ∩ Lᶜ ⊆ C \ L :=
        fun _ hy => ⟨interior_subset hy.1, hy.2⟩
      exact closure_mono hsub
        (isOpen_interior.inter_closure ⟨hLC hxl, hxc⟩)
    · exact subset_closure ⟨hxC, hxl⟩

variable [T2Space X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_originalExterior_subcomplex
    {C L : Set X} (hC : IsCompact C) (hLC : L ⊆ interior C)
    (K P : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hPK : P ≤ K)
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hHF : ∀ x : C, (H x : E) = F x) (hP : P.space = F '' L) :
    ∃ (N : SimplicialComplex ℝ E) (J : (C \ interior L : Set X) ≃ₜ N.space),
      N ≤ K ∧ N.faces.Finite ∧ N.space = F '' (C \ interior L) ∧
      (∀ x : (C \ interior L : Set X), (J x : E) = F x) ∧
      ∀ A : SimplicialComplex ℝ E, A ≤ K →
        A.space ⊆ F '' (C \ interior L) → A ≤ N := by
  have hLC' : L ⊆ C := hLC.trans interior_subset
  have hinj : InjOn F C := by
    intro x hx y hy hxy
    have hxy' : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hxy')
  have hFC : F '' C = K.space := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hHF ⟨x, hx⟩]
      exact (H ⟨x, hx⟩).property
    · intro z hz
      refine ⟨H.symm ⟨z, hz⟩, (H.symm ⟨z, hz⟩).property, ?_⟩
      exact (hHF (H.symm ⟨z, hz⟩)).symm.trans
        (congrArg Subtype.val (H.apply_symm_apply ⟨z, hz⟩))
  have hdiff : F '' (C \ L) = K.space \ P.space := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨hFC.subset ⟨x, hx.1, rfl⟩, ?_⟩
      intro hxP
      obtain ⟨y, hy, hyx⟩ := hP.subset hxP
      exact hx.2 ((hinj (hLC' hy) hx.1 hyx) ▸ hy)
    · rintro z ⟨hzK, hzP⟩
      obtain ⟨x, hx, rfl⟩ := hFC.symm.subset hzK
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro hxL
      exact hzP (hP.symm.subset ⟨x, hxL, rfl⟩)
  have hclosed : IsClosed (F '' (C \ interior L)) :=
    ((hC.diff isOpen_interior).image hF).isClosed
  have hclosure : closure (K.space \ P.space) = F '' (C \ interior L) := by
    rw [← hdiff]
    apply Subset.antisymm
    · apply closure_minimal _ hclosed
      exact image_mono (fun _ hx => ⟨hx.1, fun hi => hx.2 (interior_subset hi)⟩)
    · rw [← closure_complement_inside hC.isClosed hLC]
      exact image_closure_subset_closure_image hF
  obtain ⟨N, hNK, hN, hNs, hmarks⟩ := K.exists_closedComplement_subcomplex P hK hPK
  have hNs' : N.space = F '' (C \ interior L) := hNs.trans hclosure
  let : CompactSpace (C \ interior L : Set X) :=
    isCompact_iff_compactSpace.mp (hC.diff isOpen_interior)
  let J0 : (C \ interior L : Set X) ≃ₜ F '' (C \ interior L) :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn F (C \ interior L) (hinj.mono sdiff_subset))
      ((hF.comp continuous_subtype_val).subtype_mk _)
  let J := J0.trans (Homeomorph.setCongr hNs'.symm)
  refine ⟨N, J, hNK, hN, hNs', fun _ => rfl, ?_⟩
  intro A hAK hA
  apply hmarks A hAK
  exact hA.trans hclosure.symm.subset

end PoincareConjecture.M76
