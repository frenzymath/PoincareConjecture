import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalWholeDiskProduct

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem exists_original_unit_disk_parameter
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (j : E → X)
    (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d) :
    ∃ (H : Disk ≃ₜ d) (k : V2 → X), H.IsFinitePL ∧
      PolyhedralPLInCharts e k Disk ∧
      Topology.IsEmbedding (fun z : Disk => k z) ∧
      (∀ z : Disk, k z = j (H z)) ∧
      (∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : E) ∈ q) ∧
      k '' Disk = j '' d ∧ k '' Rim = j '' q := by
  obtain ⟨H0,hH0,hHq⟩ := hd.exists_cube_chart (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let H := H0.symm
  have hH : H.IsFinitePL := hH0.symm
  obtain ⟨u,hu,hHu⟩ := hH
  let k := j ∘ u
  have huD : MapsTo u Disk d := fun z hz => (hHu ⟨z,hz⟩) ▸ (H ⟨z,hz⟩).property
  have hkval (z : Disk) : k z = j (H z) := congrArg j (hHu z).symm
  have hkrim (z : Disk) : (z : V2) ∈ Rim ↔ (H z : E) ∈ q := by
    have hh := hHq (H z)
    rw [H0.apply_symm_apply,frontier_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hkPL : PolyhedralPLInCharts e k Disk := by
    have huCopy := hu
    obtain ⟨J,hJ,hJs,_⟩ := huCopy
    exact hJs ▸ hj.comp_finitePiecewiseAffineOn J hJ (hJs.symm ▸ hu)
      (fun z hz => huD (hJs.subset hz))
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hkemb : Topology.IsEmbedding (fun z : Disk => k z) := by
    apply (hkPL.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
    intro z w hzw
    have hh := hji (H z).property (H w).property ((hkval z).symm.trans (hzw.trans (hkval w)))
    exact H.injective (Subtype.ext hh)
  refine ⟨H,k,⟨u,hu,hHu⟩,hkPL,hkemb,hkval,hkrim,?_,?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨H ⟨z,hz⟩,(H ⟨z,hz⟩).property,(hkval ⟨z,hz⟩).symm⟩
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨H.symm ⟨z,hz⟩,(H.symm ⟨z,hz⟩).property,?_⟩
      rw [hkval,H.apply_symm_apply]
  · apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨H ⟨z,sphere_subset_closedBall hz⟩,(hkrim _).mp hz,(hkval _).symm⟩
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨H.symm ⟨z,hd.1 hz⟩,(hkrim _).mpr ?_,?_⟩
      · simpa only [H.apply_symm_apply] using hz
      · rw [hkval,H.apply_symm_apply]

end PoincareConjecture.M76
