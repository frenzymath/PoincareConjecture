import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.CrossingPatches

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace PoincareConjecture.Topology.Surface

private theorem exists_smooth_centered_regular_level_coordinates
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ ∞ f)
    {p : EuclideanSpace ℝ (Fin 2)} (hdf : fderiv ℝ f p ≠ 0) :
    ∃ G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ),
      p ∈ G.source ∧ G p = (f p, 0) ∧ (∀ z, (G z).1 = f z) ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target := by
  have hlin : (fderiv ℝ f p).toLinearMap ≠ 0 := by
    intro h
    apply hdf
    ext z
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ => L z) h
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hlin
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker (fderiv ℝ f p).toLinearMap) := by
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hdim
    omega
  have : Nontrivial (LinearMap.ker (fderiv ℝ f p).toLinearMap) :=
    Module.finrank_pos_iff.mp hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : LinearMap.ker (fderiv ℝ f p).toLinearMap)
  have hvne : (v : EuclideanSpace ℝ (Fin 2)) ≠ 0 := fun h => hv (Subtype.ext h)
  let l : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := innerSL ℝ (v : EuclideanSpace ℝ (Fin 2))
  let g := fun z : EuclideanSpace ℝ (Fin 2) => l z - l p
  have hg : ContDiff ℝ ∞ g := l.contDiff.sub contDiff_const
  have hdg : fderiv ℝ g p = l := by
    rw [fderiv_sub_const, l.fderiv]
  have hvg : fderiv ℝ g p v ≠ 0 := by
    rw [hdg]
    exact inner_self_ne_zero.mpr hvne
  obtain ⟨F, hpF, hF, _, _⟩ :=
    Poincare.Topology.Plane.Curves.exists_local_coordinates_of_transverse_levels
      hf.contDiffAt hg.contDiffAt hdf v.property hvg
  have hFeq : (F : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) = fun z => (f z, g z) := funext hF
  have hFsmooth : ContDiff ℝ ∞ F := by
    rw [hFeq]
    exact hf.prodMk hg
  obtain ⟨A, hA⟩ :=
    Poincare.Topology.Plane.Curves.exists_equiv_of_transverse_functionals hdf v.property hvg
  have hdF : HasFDerivAt F (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ)) p := by
    rw [hFeq]
    convert! ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).prodMk
      ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt) using 1
    exact ContinuousLinearMap.ext hA
  obtain ⟨G, hpG, hG, _, hGon, hGinv⟩ :=
    exists_smooth_coordinate_restriction F hpF isOpen_univ (mem_univ p)
      hFsmooth.contDiffOn A hdF
  refine ⟨G, hpG, ?_, fun z => ?_, hGon, hGinv⟩
  · rw [hG, hF]
    simp [g]
  · rw [hG, hF]

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

theorem exists_chartCircle_vertex_coordinates [IsManifold (𝓡 2) ∞ M]
    (x : M) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    {p : M} (hp : p ∈ chartCircle x r) :
    ∃ C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M,
      p ∈ C.target ∧ C.symm p = 0 ∧
      C.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      (∀ z ∈ C.source,
        ‖chartAt (EuclideanSpace ℝ (Fin 2)) x (C z) -
          chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2 - r ^ 2 = z 0) ∧
      (∀ z ∈ C.source, C z ∈ chartCircle x r ↔ z 0 = 0) := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let f := fun z : EuclideanSpace ℝ (Fin 2) => ‖z - e x‖ ^ 2 - r ^ 2
  have hps := chartCircle_subset_chart_source x hsub hp
  have hf : ContDiff ℝ ∞ f :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const
  have hdf : fderiv ℝ f (e p) ≠ 0 := by
    rw [fderiv_sub_const]
    exact (chartCircle_coordinateSquaredRadius_regular x hr hsub hp).2
  have hfp : f (e p) = 0 :=
    sub_eq_zero.mpr ((mem_chartCircle_iff_norm_sq x hr hsub hps).mp hp)
  obtain ⟨G, hpG, hGp, hGfst, hG, hGinv⟩ :=
    exists_smooth_centered_regular_level_coordinates hf hdf
  let L := collarParameterEquiv
  let H := L.toHomeomorph.toOpenPartialHomeomorph.trans G.symm
  let C := H.trans e.symm
  have hH : ContDiffOn ℝ ∞ H H.source :=
    hGinv.comp L.contDiff.contDiffOn (fun _ hz => hz.2)
  have hHinv : ContDiffOn ℝ ∞ H.symm H.target :=
    L.symm.contDiff.comp_contDiffOn (hG.mono (fun _ hz => hz.1))
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := x)).comp
      (hH.contMDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    hHinv.contMDiffOn.comp
      ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := x)).mono (fun _ hz => hz.1))
      (fun _ hz => hz.2)
  have hcoords (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ C.source) :
      ‖e (C z) - e x‖ ^ 2 - r ^ 2 = z 0 := by
    have h := congrArg Prod.fst (G.right_inv hz.1.2)
    rw [hGfst] at h
    change ‖e (e.symm (G.symm (L z))) - e x‖ ^ 2 - r ^ 2 = z 0
    rw [e.right_inv (show G.symm (L z) ∈ e.target from hz.2)]
    exact h
  refine ⟨C, ⟨hps, hpG, mem_univ _⟩, ?_, fun _ hz => hz.1, hC, hCinv, hcoords, ?_⟩
  · change L.symm (G (e p)) = 0
    rw [hGp, hfp]
    exact map_zero L.symm
  · intro z hz
    rw [mem_chartCircle_iff_norm_sq x hr hsub (C.map_source hz).1]
    rw [← hcoords z hz, sub_eq_zero]

structure ChartCircleVertexPatch (x : M) (r : ℝ) (p : M) where
  coordinates : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M
  width : ℝ
  width_pos : 0 < width
  point_mem : p ∈ coordinates.target
  center_eq : coordinates.symm p = 0
  target_subset : coordinates.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source
  smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ coordinates coordinates.source
  smooth_symm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ coordinates.symm coordinates.target
  rectangle_subset : crossingClosedRectangle 0 0 width ⊆ coordinates.source
  squaredRadius : ∀ z ∈ coordinates.source,
    ‖chartAt (EuclideanSpace ℝ (Fin 2)) x (coordinates z) -
      chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2 - r ^ 2 = z 0
  circle : ∀ z ∈ coordinates.source, coordinates z ∈ chartCircle x r ↔ z 0 = 0

namespace ChartCircleVertexPatch

variable {x p : M} {r : ℝ} (P : ChartCircleVertexPatch x r p)

def openCarrier : Set M := P.coordinates '' crossingOpenRectangle 0 0 P.width

def carrier : Set M := P.coordinates '' crossingClosedRectangle 0 0 P.width

theorem openCarrier_subset_carrier : P.openCarrier ⊆ P.carrier :=
  image_mono (crossingOpenRectangle_subset_closed _ _ _)

theorem isOpen_openCarrier : IsOpen P.openCarrier :=
  P.coordinates.isOpen_image_of_subset_source (isOpen_crossingOpenRectangle _ _ _)
    ((crossingOpenRectangle_subset_closed _ _ _).trans P.rectangle_subset)

theorem mem_openCarrier : p ∈ P.openCarrier := by
  refine ⟨P.coordinates.symm p, ?_, P.coordinates.right_inv P.point_mem⟩
  rw [P.center_eq]
  change collarParameterEquiv 0 ∈ ball (0, 0) P.width
  rw [map_zero]
  exact mem_ball_self P.width_pos

theorem isCompact_carrier : IsCompact P.carrier :=
  (isCompact_crossingClosedRectangle _ _ _).image_of_continuousOn
    (P.coordinates.continuousOn.mono P.rectangle_subset)

theorem carrier_subset_target : P.carrier ⊆ P.coordinates.target := by
  rintro _ ⟨z, hz, rfl⟩
  exact P.coordinates.map_source (P.rectangle_subset hz)

variable [T2Space M]

theorem closure_openCarrier : closure P.openCarrier = P.carrier := by
  apply subset_antisymm
  · exact closure_minimal P.openCarrier_subset_carrier P.isCompact_carrier.isClosed
  · rintro _ ⟨z, hz, rfl⟩
    have hzclosure : z ∈ closure (crossingOpenRectangle 0 0 P.width) := by
      rwa [closure_crossingOpenRectangle _ _ P.width_pos]
    exact mem_closure_image (P.coordinates.continuousAt (P.rectangle_subset hz)) hzclosure

theorem isCompact_closure_openCarrier : IsCompact (closure P.openCarrier) := by
  rw [P.closure_openCarrier]
  exact P.isCompact_carrier

end ChartCircleVertexPatch

theorem exists_chartCircle_vertex_patch [IsManifold (𝓡 2) ∞ M]
    (x : M) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    {p : M} (hp : p ∈ chartCircle x r) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ P : ChartCircleVertexPatch x r p, P.carrier ⊆ N := by
  obtain ⟨C, hpC, hcenter, htarget, hC, hCinv, hradius, hcircle⟩ :=
    exists_chartCircle_vertex_coordinates x hr hsub hp
  have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ C.source := by
    rw [← hcenter]
    exact C.map_target hpC
  have hCzero : C 0 = p := by
    rw [← hcenter]
    exact C.right_inv hpC
  have hsource : C.source ∩ C ⁻¹' N ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)) :=
    Filter.inter_mem (C.open_source.mem_nhds hzero)
      ((C.continuousAt hzero).preimage_mem_nhds (hCzero.symm ▸ hN))
  have hproduct : collarParameterEquiv.symm ⁻¹' (C.source ∩ C ⁻¹' N) ∈
      𝓝 (0 : ℝ × ℝ) := by
    apply collarParameterEquiv.symm.continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using hsource
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hproduct
  have hrectangle : crossingClosedRectangle 0 0 (δ / 2) ⊆ C.source ∩ C ⁻¹' N := by
    intro z hz
    have hz' : collarParameterEquiv z ∈ ball (0 : ℝ × ℝ) δ :=
      closedBall_subset_ball (half_lt_self hδ) hz
    have h := hδsub hz'
    change collarParameterEquiv.symm (collarParameterEquiv z) ∈ C.source ∩ C ⁻¹' N at h
    simpa only [collarParameterEquiv.symm_apply_apply] using h
  let P : ChartCircleVertexPatch x r p := {
    coordinates := C
    width := δ / 2
    width_pos := half_pos hδ
    point_mem := hpC
    center_eq := hcenter
    target_subset := htarget
    smooth := hC
    smooth_symm := hCinv
    rectangle_subset := fun _ hz => (hrectangle hz).1
    squaredRadius := hradius
    circle := hcircle }
  refine ⟨P, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (hrectangle hz).2

end PoincareConjecture.Topology.Surface
