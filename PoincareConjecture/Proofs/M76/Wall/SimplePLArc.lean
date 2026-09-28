import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierArc
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLNeighborhoodModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem exists_simple_polyhedralPL_arc_in_image
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hconn : IsConnected K.space) {f : E → X}
    (hf : PolyhedralPLInCharts e f K.space)
    {a b : E} (ha : a ∈ K.space) (hb : b ∈ K.space) (hab : f a ≠ f b) :
    ∃ q : ℝ → X, PolyhedralPLInCharts e q (Icc (0 : ℝ) 1) ∧
      InjOn q (Icc (0 : ℝ) 1) ∧ q 0 = f a ∧ q 1 = f b ∧
      q '' Icc (0 : ℝ) 1 ⊆ f '' K.space := by
  classical
  have hA : IsCompact (f '' K.space) :=
    (K.isCompact_space_of_finite hK).image_of_continuousOn hf.continuousOn
  obtain ⟨s, Fmap, C, N, H, _, hAC, _, _, hFc, hFPL, hH, hcharts⟩ :=
    exists_compact_PL_neighborhood_model e hcompat hcover hA isOpen_univ
      (subset_univ _)
  have hfC : MapsTo f K.space C := fun _ hx =>
    interior_subset (hAC (mem_image_of_mem f hx))
  have hFi : InjOn Fmap C := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))))
  have hFf := hf.finitePiecewiseAffineOn_comp K hK hFPL
  obtain ⟨J, hJ, hJs⟩ := hFf.exists_finite_triangulation_image
  have hJconn : IsConnected J.space := by
    rw [hJs]
    exact hconn.image _ (hFc.comp_continuousOn hf.continuousOn)
  have haJ : Fmap (f a) ∈ J.space := hJs.symm.subset ⟨a, ha, rfl⟩
  have hbJ : Fmap (f b) ∈ J.space := hJs.symm.subset ⟨b, hb, rfl⟩
  have habF : Fmap (f a) ≠ Fmap (f b) :=
    fun h => hab (hFi (hfC ha) (hfC hb) h)
  obtain ⟨T, P, _, hTJ, ⟨g, hg, hPg⟩, hP0, hP1⟩ :=
    J.exists_finitePL_arc_in_carrier hJ hJconn haJ hbJ habF
  have hgT : MapsTo g (Icc (0 : ℝ) 1) T := by
    intro x hx
    rw [← hPg ⟨x, hx⟩]
    exact (P ⟨x, hx⟩).property
  have hJN : J.space ⊆ N.space := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hJs.subset hz
    rw [Function.comp_apply, ← hH ⟨f x, hfC hx⟩]
    exact (H ⟨f x, hfC hx⟩).property
  have hgN : MapsTo g (Icc (0 : ℝ) 1) N.space :=
    fun _ hx => hJN (hTJ (hgT hx))
  let q : ℝ → X := fun x => if hx : x ∈ Icc (0 : ℝ) 1 then
    (H.symm ⟨g x, hgN hx⟩ : X) else f a
  have hq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      q x = (H.symm ⟨g x, hgN hx⟩ : X) := by
    dsimp only [q]
    rw [dif_pos hx]
  have hgc : Continuous (fun x : Icc (0 : ℝ) 1 =>
      (⟨g x, hgN x.property⟩ : N.space)) :=
    hg.continuousOn.domRestrict.subtype_mk _
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp (H.symm.continuous.comp hgc)).congr
      (fun x => (hq x x.property).symm)
  have hqC : MapsTo q (Icc (0 : ℝ) 1) C := by
    intro x hx
    rw [hq x hx]
    exact (H.symm ⟨g x, hgN hx⟩).property
  have hFq : EqOn (Fmap ∘ q) g (Icc (0 : ℝ) 1) := by
    intro x hx
    change Fmap (q x) = g x
    rw [hq x hx]
    exact (hH (H.symm ⟨g x, hgN hx⟩)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨g x, hgN hx⟩))
  have hqPL : PolyhedralPLInCharts e q (Icc (0 : ℝ) 1) := by
    obtain ⟨L, hL, hLs, hgL⟩ := hg
    rw [← hLs] at hqc hqC hFq ⊢
    exact polyhedralPLInCharts_of_affine_projections e Fmap C hcharts L hL
      hqc hqC (hgL.finitePiecewiseAffineOn hL) hFq
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨q, hqPL, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hPxy : P ⟨x, hx⟩ = P ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [hPg, hPg, ← hFq hx, ← hFq hy]
      exact congrArg Fmap hxy
    exact congrArg Subtype.val (P.injective hPxy)
  · apply hFi (hqC hzero) (hfC ha)
    exact (hFq hzero).trans ((hPg ⟨0, hzero⟩).symm.trans hP0)
  · apply hFi (hqC hone) (hfC hb)
    exact (hFq hone).trans ((hPg ⟨1, hone⟩).symm.trans hP1)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hJs.subset (hTJ (hgT hx))
    refine ⟨y, hy, hFi (hfC hy) (hqC hx) ?_⟩
    exact hyx.trans (hFq hx).symm

end OpenPartialHomeomorph
