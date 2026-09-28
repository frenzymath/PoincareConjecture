import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SelectedCircleSurgeryGraph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.NonreturningSubcomplex
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.CircleFreeSubcomplex
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.TriangleArcGraphPosition

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem InNonreturningTriangleGraphPosition.selected_circle_surgery
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X] [Finite κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool)
    (sfull : ∀ j, ChartwisePLSphere e (circleSurgeryFamily S i new j))
    (hfull : Pairwise fun j k => Disjoint (circleSurgeryFamily S i new j)
      (circleSurgeryFamily S i new k))
    {Q : OpenPartialHomeomorph X V3} {g : E → X} {s : Finset E} {A : E →ᴬ[ℝ] V3}
    (h : InNonreturningTriangleGraphPosition Q (⋃ j, circleSurgeryFamily S i new j) g s A) :
    InNonreturningTriangleGraphPosition Q (⋃ j, selectedCircleSurgeryFamily S i new b j)
      g s A := by
  classical
  obtain ⟨G, hG, hGT, hdim, hphysical, hint, hext, hfront, hcross, hreturn⟩ := h
  obtain ⟨H, hHG, hH, hspace, himage, _, hdegree⟩ :=
    exists_selected_circle_surgery_graph S i new b sfull hfull Q G hG
      (hGT.trans inter_subset_right) hphysical
  have hsub : H.space ⊆ G.space := hspace ▸ inter_subset_left
  refine ⟨H, hH, hsub.trans hGT, (fun a ha => hdim a (hHG ha)), himage,
    ?_, ?_, hfront.subset (inter_subset_inter_left _ hsub), ?_,
    G.nonreturning_of_subcomplex H hG hHG hdegree s A hreturn⟩
  · intro v hv
    exact (hdegree v).trans (hint ⟨v.val, hHG v.property⟩ hv)
  · intro v hv
    exact (hdegree v).trans (hext ⟨v.val, hHG v.property⟩ hv)
  · intro w hw
    have hwH := hw.1
    rw [hspace] at hwH
    exact selected_circle_surgery_paired_crossings S i new b sfull hfull Q
      (hGT hwH.1).2 hwH.2 (hcross w ⟨hwH.1, hw.2⟩)

theorem InCircleFreeNonreturningTriangleGraphPosition.selected_circle_surgery
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X] [Finite κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool)
    (sfull : ∀ j, ChartwisePLSphere e (circleSurgeryFamily S i new j))
    (hfull : Pairwise fun j k => Disjoint (circleSurgeryFamily S i new j)
      (circleSurgeryFamily S i new k))
    {Q : OpenPartialHomeomorph X V3} {g : E → X} {s : Finset E} {A : E →ᴬ[ℝ] V3}
    (h : InCircleFreeNonreturningTriangleGraphPosition Q
      (⋃ j, circleSurgeryFamily S i new j) g s A) :
    InCircleFreeNonreturningTriangleGraphPosition Q
      (⋃ j, selectedCircleSurgeryFamily S i new b j) g s A := by
  classical
  obtain ⟨G, hG, hGT, hdim, hphysical, hint, hext, hfront, hcross, hreturn, hfree⟩ := h
  obtain ⟨H, hHG, hH, hspace, himage, _, hdegree⟩ :=
    exists_selected_circle_surgery_graph S i new b sfull hfull Q G hG
      (hGT.trans inter_subset_right) hphysical
  have hsub : H.space ⊆ G.space := hspace ▸ inter_subset_left
  refine ⟨H, hH, hsub.trans hGT, (fun a ha => hdim a (hHG ha)), himage,
    ?_, ?_, hfront.subset (inter_subset_inter_left _ hsub), ?_,
    G.nonreturning_of_subcomplex H hG hHG hdegree s A hreturn,
    G.component_segmentCarrier_meets_of_subcomplex H hG hHG hdegree _ hfree⟩
  · intro v hv
    exact (hdegree v).trans (hint ⟨v.val, hHG v.property⟩ hv)
  · intro v hv
    exact (hdegree v).trans (hext ⟨v.val, hHG v.property⟩ hv)
  · intro w hw
    have hwH := hw.1
    rw [hspace] at hwH
    exact selected_circle_surgery_paired_crossings S i new b sfull hfull Q
      (hGT hwH.1).2 hwH.2 (hcross w ⟨hwH.1, hw.2⟩)

end PoincareConjecture.M76
