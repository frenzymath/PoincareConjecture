import PoincareConjecture.Proofs.M76.Mathlib.ProductCellComplement

set_option autoImplicit false

open Set Metric

theorem Metric.thickening_prod {E F : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace F] (δ : ℝ) (s : Set E) (t : Set F) :
    thickening δ (s ×ˢ t) = thickening δ s ×ˢ thickening δ t := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨u, v⟩, huv, hd⟩ := mem_thickening_iff.mp hx
    have hdist : dist x.1 u < δ ∧ dist x.2 v < δ := max_lt_iff.mp hd
    exact ⟨mem_thickening_iff.mpr ⟨u, huv.1, hdist.1⟩,
      mem_thickening_iff.mpr ⟨v, huv.2, hdist.2⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨u, hu, hdu⟩ := mem_thickening_iff.mp hx
    obtain ⟨v, hv, hdv⟩ := mem_thickening_iff.mp hy
    exact mem_thickening_iff.mpr ⟨(u, v), ⟨hu, hv⟩, max_lt_iff.mpr ⟨hdu, hdv⟩⟩

theorem isSimplyConnected_thickening_sdiff_product_cell
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hdim : 2 < Module.finrank ℝ (E × F))
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    IsSimplyConnected (thickening δ (closedBall (0 : E) r ×ˢ {(0 : F)}) \
      (closedBall (0 : E) r ×ˢ {(0 : F)})) := by
  rw [thickening_prod, thickening_closedBall hδ hr, thickening_singleton, add_comm δ r]
  exact isSimplyConnected_product_cell_tube hdim hr hδ

namespace OpenPartialHomeomorph

theorem exists_simplyConnected_deleted_cell_neighborhood
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (hdim : 2 < Module.finrank ℝ (E × F)) (Q : OpenPartialHomeomorph (E × F) X)
    {r : ℝ} (hr : 0 ≤ r) (hsource : closedBall (0 : E) r ×ˢ {(0 : F)} ⊆ Q.source)
    {W : Set X} (hW : IsOpen W) (hCW : Q '' (closedBall (0 : E) r ×ˢ {(0 : F)}) ⊆ W) :
    ∃ V : Set X, IsOpen V ∧ Q '' (closedBall (0 : E) r ×ˢ {(0 : F)}) ⊆ V ∧
      closure V ⊆ W ∧ IsCompact (closure V) ∧
      IsSimplyConnected (V \ Q '' (closedBall (0 : E) r ×ˢ {(0 : F)})) := by
  let C : Set (E × F) := closedBall (0 : E) r ×ˢ {(0 : F)}
  have hC : IsCompact C := (isCompact_closedBall (0 : E) r).prod isCompact_singleton
  have hD : IsOpen (Q.source ∩ Q ⁻¹' W) :=
    Q.continuousOn_toFun.isOpen_inter_preimage Q.open_source hW
  have hCD : C ⊆ Q.source ∩ Q ⁻¹' W :=
    fun x hx => ⟨hsource hx, hCW ⟨x, hx, rfl⟩⟩
  obtain ⟨δ, hδ, hδD⟩ := hC.exists_cthickening_subset_open hD hCD
  have hthick : thickening δ C ⊆ Q.source :=
    (thickening_subset_cthickening δ C).trans (hδD.trans inter_subset_left)
  let V : Set X := Q '' thickening δ C
  let D : Set X := Q '' cthickening δ C
  have hDc : IsCompact D := hC.cthickening.image_of_continuousOn
    (Q.continuousOn_toFun.mono (hδD.trans inter_subset_left))
  have hVD : closure V ⊆ D :=
    closure_minimal (image_mono (thickening_subset_cthickening δ C)) hDc.isClosed
  refine ⟨V, Q.isOpen_image_of_subset_source isOpen_thickening hthick,
    image_mono (self_subset_thickening hδ C), ?_,
    hDc.of_isClosed_subset isClosed_closure hVD, ?_⟩
  · rintro x hx
    obtain ⟨z, hz, rfl⟩ := hVD hx
    exact (hδD hz).2
  · change IsSimplyConnected ((Q '' thickening δ C) \ Q '' C)
    rw [← (Q.injOn.mono hthick).image_sdiff_subset (self_subset_thickening hδ C)]
    exact Q.isSimplyConnected_image_of_subset_source (sdiff_subset.trans hthick)
      (isSimplyConnected_thickening_sdiff_product_cell hdim hr hδ)

theorem exists_compact_core_simplyConnected_deleted_cell_complement
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (hdim : 2 < Module.finrank ℝ (E × F)) (Q : OpenPartialHomeomorph (E × F) X)
    {r : ℝ} (hr : 0 ≤ r) (hsource : closedBall (0 : E) r ×ˢ {(0 : F)} ⊆ Q.source)
    {A : Set X} (hA : IsCompact A)
    (hdis : Disjoint A (Q '' (closedBall (0 : E) r ×ˢ {(0 : F)}))) :
    ∃ K : Set X, IsCompact K ∧ A ⊆ interior K ∧
      Disjoint K (Q '' (closedBall (0 : E) r ×ˢ {(0 : F)})) ∧
      IsSimplyConnected (Kᶜ \ Q '' (closedBall (0 : E) r ×ˢ {(0 : F)})) := by
  have hCA : Q '' (closedBall (0 : E) r ×ˢ {(0 : F)}) ⊆ Aᶜ :=
    fun x hx hxA => disjoint_left.mp hdis hxA hx
  obtain ⟨V, hV, hCV, hVA, _, hsc⟩ :=
    Q.exists_simplyConnected_deleted_cell_neighborhood hdim hr hsource
      hA.isClosed.isOpen_compl hCA
  refine ⟨Vᶜ, hV.isClosed_compl.isCompact, ?_, ?_, ?_⟩
  · rw [interior_compl]
    exact fun x hx hxV => hVA hxV hx
  · exact disjoint_left.mpr fun x hx hxC => hx (hCV hxC)
  · simpa only [compl_compl] using hsc

end OpenPartialHomeomorph
