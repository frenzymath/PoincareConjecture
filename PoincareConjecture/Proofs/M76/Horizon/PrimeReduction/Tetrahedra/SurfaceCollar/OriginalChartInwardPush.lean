import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.ConvexPlanarBoundaryPush
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartPLTransition
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_original_chart_inward_push
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X E)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (B : OpenPartialHomeomorph X E)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E)
    {R S O : Set X} {V C : Set E} (hO : IsOpen O) (hV : IsOpen V)
    (hVT : V ⊆ B.target) (hC : Convex ℝ C)
    (hR : ∀ z ∈ V, B.symm z ∈ R ↔ z ∈ C)
    (A : E →ᵃ[ℝ] ℝ) (hS : ∀ z ∈ V, B.symm z ∈ S ↔ A z = 0)
    {y : X} (hyB : y ∈ B.source) (hyV : B y ∈ V) (hyR : y ∈ R)
    (hyO : y ∈ O) {w : E} (hw : w ∈ interior C) (hAw : A w = A (B y)) :
    ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E) ∧
      EqOn H id Oᶜ ∧ (∀ x, H x ∈ S ↔ x ∈ S) ∧
      (∀ x ∈ R, H x ∈ interior R ∨ H x = x) ∧ H y ∈ interior R := by
  classical
  let U := V ∩ (B.target ∩ B.symm ⁻¹' O)
  have hU : IsOpen U := hV.inter (B.symm.isOpen_inter_preimage hO)
  have hyU : B y ∈ U := ⟨hyV, B.map_source hyB, by
    simpa only [mem_preimage, B.left_inv hyB] using hyO⟩
  obtain ⟨K,hK,hyK,hKU⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    isCompact_singleton hU (singleton_subset_iff.mpr hyU)
  have hKV : K.space ⊆ V := fun _ hz => (hKU hz).1
  have hKT : K.space ⊆ B.target := hKV.trans hVT
  have hyC : B y ∈ C := (hR (B y) hyV).mp (by simpa only [B.left_inv hyB] using hyR)
  obtain ⟨G,hGPL,_,hGfix,hGA,hGin,hGy⟩ := exists_supported_convex_plane_push hC
    isOpen_interior hyC (hyK (mem_singleton _)) hw A hAw
  have hGout : EqOn G id K.spaceᶜ := fun _ hz => hGfix (fun hi => hz (interior_subset hi))
  have hGKV : MapsTo G K.space K.space := by
    intro z hz
    by_contra hn
    have heq : G z = z := G.injective (hGout hn)
    exact hn (heq.symm ▸ hz)
  have hGPL' : G.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E := by
    apply G.toOpenPartialHomeomorph.mem_piecewiseAffineGroupoid_of_local_finitePL
    intro z _
    obtain ⟨L,hL,hzL,_⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
      (isCompact_singleton : IsCompact ({z} : Set E)) isOpen_univ (subset_univ _)
    exact ⟨L.space,hzL (mem_singleton _),hGPL L hL⟩
  obtain ⟨H,hHB,hHout⟩ := B.symm.exists_supported_chart_homeomorph G
    (K.isCompact_space_of_finite hK) hKT hGout
  have hHformula {x : X} (hx : x ∈ B.source) : H x = B.symm (G (B x)) := hHB hx
  have hforward (i j : ι) :
      (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid E :=
    B.symm.supported_chart_transition_mem_piecewiseAffineGroupoid
      (e i).symm (e j).symm G H (K.isCompact_space_of_finite hK) hKT hGout
      hHB hHout hGPL' (hB i) (hB j) (he i j)
  have hphysicalInterior {z : E} (hz : z ∈ interior C) (hzV : z ∈ V) :
      B.symm z ∈ interior R := by
    have hopen : IsOpen (B.symm '' (interior C ∩ V)) :=
      B.symm.isOpen_image_of_subset_source (isOpen_interior.inter hV)
        (fun _ h => hVT h.2)
    apply (interior_maximal ?_ hopen) (mem_image_of_mem _ ⟨hz,hzV⟩)
    rintro _ ⟨a,ha,rfl⟩
    exact (hR a ha.2).mpr (interior_subset ha.1)
  refine ⟨H,hforward,?_,?_,?_,?_,?_⟩
  · intro i j
    have hinv := (piecewiseAffineGroupoid E).symm (hforward j i)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using hinv
  · intro x hx
    apply hHout
    rintro ⟨z,hz,rfl⟩
    exact hx (hKU hz).2.2
  · intro x
    by_cases hx : x ∈ B.symm '' K.space
    · obtain ⟨z,hz,rfl⟩ := hx
      rw [hHformula (B.map_target (hKT hz)),B.right_inv (hKT hz),
        hS _ (hKV (hGKV hz)),hS _ (hKV hz),hGA]
    · rw [show H x = x from hHout hx]
  · intro x hxR
    by_cases hx : x ∈ B.symm '' K.space
    · obtain ⟨z,hz,rfl⟩ := hx
      have hzC := (hR z (hKV hz)).mp hxR
      rw [hHformula (B.map_target (hKT hz)),B.right_inv (hKT hz)]
      rcases hGin z hzC with hi | hf
      · exact Or.inl (hphysicalInterior hi (hKV (hGKV hz)))
      · exact Or.inr (congrArg B.symm hf)
    · exact Or.inr (hHout hx)
  · rw [hHformula hyB]
    exact hphysicalInterior hGy (hKV (hGKV (interior_subset (hyK (mem_singleton _)))))

end PoincareConjecture.M76
