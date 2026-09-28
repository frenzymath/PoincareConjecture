


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

omit [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
private theorem frontier_coordinate_image
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hcompact : IsCompact K)
    (hK : K ⊆ F.source) : frontier (F '' K) = F '' frontier K := by
  have himage : F '' K ⊆ F.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact F.map_source (hK hz)
  have hcimage := hcompact.image_of_continuousOn (F.continuousOn.mono hK)
  have hisimage : F.IsImage K (F '' K) := by
    intro z hz
    constructor
    · rintro ⟨w, hw, heq⟩
      exact F.injOn (hK hw) hz heq ▸ hw
    · exact mem_image_of_mem F
  simpa only [inter_eq_right.mpr (hcompact.isClosed.frontier_subset.trans hK),
    inter_eq_right.mpr (hcimage.isClosed.frontier_subset.trans himage)] using
    hisimage.frontier.image_eq.symm

private theorem segment_image (a b : EuclideanSpace ℝ (Fin 2)) :
    affineChartSegment a b '' Icc (0 : ℝ) 1 = affineSegment ℝ a b := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

omit [T2Space M] in


theorem exists_smoothEdge_of_smooth_coordinates
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {a b : EuclideanSpace ℝ (Fin 2)} (hab : a ≠ b)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, affineChartSegment a b t ∈ F.source) :
    ∃ e : SmoothEdge M, e.map = F ∘ affineChartSegment a b ∧
      InjOn e.map (Icc (0 : ℝ) 1) ∧ e.map 0 = F a ∧ e.map 1 = F b := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hsm : ContDiff ℝ ∞ (affineChartSegment a b) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hd (t : ℝ) : HasFDerivAt (affineChartSegment a b)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (b - a)) t :=
    ((hasFDerivAt_id t).smul_const (b - a)).const_add a
  have hdiff : F.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hF.mdifferentiableOn (by simp), hFinv.mdifferentiableOn (by simp)⟩
  let e : SmoothEdge M := {
    map := F ∘ affineChartSegment a b
    smooth := hF.comp hsm.contMDiff.contMDiffOn hseg
    regular := by
      intro t ht
      have hsource := hseg t ⟨ht.1.le, ht.2.le⟩
      rw [mfderiv_comp t (hdiff.mdifferentiableAt hsource)
        (hd t).differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, (hd t).fderiv]
      exact (hdiff.mfderiv_injective hsource).comp (smul_left_injective ℝ hba) }
  refine ⟨e, rfl, ?_, ?_, ?_⟩
  · intro s hs t ht h
    have heq := F.injOn (hseg s hs) (hseg t ht) h
    exact smul_left_injective ℝ hba (add_left_cancel heq)
  · simp [e, affineChartSegment]
  · simp [e, affineChartSegment]



theorem exists_smoothFace_of_smooth_coordinates
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : convexHull ℝ (range b) ⊆ F.source) (p : M)
    (hchart : F '' convexHull ℝ (range b) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ∃ f : SmoothFace M, f.map = F ∧ f.source = convexHull ℝ (range b) ∧
      f.carrier = F '' convexHull ℝ (range b) ∧ InjOn f.map f.source ∧
      ∀ i : Fin 3, (f.boundary i).map =
        F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) := by
  classical
  have hseg (i : Fin 3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) t ∈ F.source := by
    apply hsub
    apply segment_subset_convexHull (mem_range_self (i.succAbove 0))
      (mem_range_self (i.succAbove 1))
    rw [← affineSegment_eq_segment, ← segment_image]
    exact mem_image_of_mem _ ht
  have hne (i : Fin 3) : b (i.succAbove 0) ≠ b (i.succAbove 1) := by
    intro h
    have hi : (0 : Fin 2) = 1 :=
      (Fin.succAbove_right_injective (p := i)) (b.ind.injective h)
    norm_num at hi
  choose edge hedge hinj hstart hend using fun i : Fin 3 =>
    exists_smoothEdge_of_smooth_coordinates F hF hFinv (hne i) (hseg i)
  let f : SmoothFace M := {
    map := F
    source := convexHull ℝ (range b)
    source_compact := (finite_range b).isCompact_convexHull ℝ
    source_triangle := by
      refine ⟨b 0, b 1, b 2, ?_⟩
      congr 1
      ext y
      simp only [mem_range, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
    smooth := hF.mono hsub
    carrier := F '' convexHull ℝ (range b)
    carrier_eq_image := rfl
    chart := p
    carrier_subset_chart := hchart
    boundary := edge
    boundary_carrier := by
      rw [frontier_coordinate_image F ((finite_range b).isCompact_convexHull ℝ) hsub,
        frontier_convexHull_affineBasis_fin3_segments, image_iUnion]
      congr 1
      funext i
      rw [hedge i, ← segment_image, image_image]
      rfl }
  exact ⟨f, rfl, rfl, rfl, F.injOn.mono hsub, hedge⟩

end PoincareConjecture.Topology.Surface
