import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapBandRays
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.EndpointFans









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology
open Poincare.Topology.Plane.Triangles Poincare.Topology.Plane.Curves
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in
private theorem regular_curve_velocity_pos_smul_of_coordinate_image
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source) {i j : Fin 3} (hij : i ≠ j)
    {η : ℝ → S} (hη : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ η t)
    (hinj : InjOn η (Icc (0 : ℝ) 1))
    (hreg : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) η 0 1 ≠ 0)
    (himage : MapsTo η (Icc (0 : ℝ) 1)
      ((fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) '' Icc (0 : ℝ) 1))
    (hpoint : η 0 = F (b i)) :
    ∃ a : ℝ, 0 < a ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) η 0 1 = a • coordinateTriangleVelocity F b i j := by
  let γ := fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)
  let e := coordinateTriangleChart F b
  let p := standardTriangleVertex i
  let v := standardTriangleVertex j - standardTriangleVertex i
  have hmap (t : ℝ) : e.symm (p + t • v) = γ t := by
    simpa only [e, p, v, γ, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
      using coordinateTriangleChart_side F b i j t
  have hv : v ≠ 0 := by
    intro hz
    have h := congrArg (triangleParameterEquiv b) (sub_eq_zero.mp hz)
    rw [triangleParameterEquiv_vertex, triangleParameterEquiv_vertex] at h
    exact hij (b.ind.injective h).symm
  have htarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p + t • v ∈ e.target := by
    change p + t • v ∈ ((triangleParameterEquiv b).toHomeomorph.toOpenPartialHomeomorph.trans F).source
    refine ⟨mem_univ _, hb ?_⟩
    change triangleParameterEquiv b (p + t • v) ∈ convexHull ℝ (range b)
    have heq : p + t • v = AffineMap.lineMap (standardTriangleVertex i) (standardTriangleVertex j) t := by
      simp [p, v, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    rw [heq, triangleParameterEquiv_side]
    exact (convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self i)) (subset_convexHull ℝ _ (mem_range_self j)) ht
  obtain ⟨φ, hφ, hmaps, heq, huniq⟩ := LeviCivitaData.exists_smooth_chart_edge_parameter
    e (coordinateTriangleChart_smooth F b hFi) p v hv htarget hη (by simpa only [hmap] using himage)
  have heq' : EqOn η (γ ∘ φ) (Icc (0 : ℝ) 1) := by
    intro t ht
    simpa only [Function.comp_apply, hmap] using heq t ht
  have hzero : φ 0 = 0 := by
    apply huniq 0 (by simp) 0 (by simp)
    rw [hmap]
    simpa only [γ, AffineMap.lineMap_apply_zero] using hpoint
  have hφinj : InjOn φ (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    apply hinj hs ht
    rw [heq' hs, heq' ht, Function.comp_apply, Function.comp_apply, he]
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn φ (Icc (0 : ℝ) 1) := by
    rcases hcont.strictMonoOn_of_injOn_Icc' zero_le_one hφinj with hm | hm
    · exact hm
    · have hn := hm (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1) zero_lt_one
      have hp := (hmaps (by simp : (1 : ℝ) ∈ Icc 0 1)).1
      rw [hzero] at hn
      exact (not_lt_of_ge hp hn).elim
  have hdiff : DifferentiableAt ℝ φ 0 := (hφ 0 (by simp)).differentiableAt (by simp)
  have hnonneg : 0 ≤ deriv φ 0 := by
    have h := hmono.monotoneOn.derivWithin_nonneg (x := 0)
    rwa [hdiff.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 (by simp))] at h
  have hvelocity := mfderiv_curve_reparam_zero_of_eqOn
    ((coordinateTriangle_side_velocity F b hF hFi hb i j (by simp : (0 : ℝ) ∈ Icc 0 1)).1.mdifferentiableAt (by simp))
    ((hη 0 (by simp)).mdifferentiableAt (by simp)) hdiff hzero heq'
  have hne : deriv φ 0 ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hvelocity
    exact hreg hvelocity
  exact ⟨deriv φ 0, lt_of_le_of_ne hnonneg hne.symm, hvelocity⟩

namespace FiniteChartRegionDecomposition

variable (D : FiniteChartRegionDecomposition (M := S))

theorem edgeFromEndpoint_terminal_velocity (e : D.EdgeIndex) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edgeFromEndpoint e true) t 1 =
      -mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map (1 - t) 1 := by
  have hφ : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have h := LeviCivitaData.mfderiv_curve_reparam
    ((D.edge_contMDiff e).mdifferentiable (by simp) (1 - t)) hφ
  exact h.trans (neg_one_smul ℝ _)

theorem edgeFromEndpoint_velocity_ne_zero (e : D.EdgeIndex) (terminal : Bool) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edgeFromEndpoint e terminal) t 1 ≠ 0 := by
  have hbase (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map s 1 ≠ 0 := by
    intro h
    exact (one_ne_zero : (1 : ℝ) ≠ 0)
      ((D.edge_mfderiv_injective e s) (h.trans (map_zero _).symm))
  cases terminal
  · exact hbase t
  · have hφ : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h := LeviCivitaData.mfderiv_curve_reparam
      ((D.edge_contMDiff e).mdifferentiable (by simp) (1 - t)) hφ
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edgeFromEndpoint e true) t 1 = _ at h
    rw [h]
    exact smul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) (hbase (1 - t))

namespace CapGraphEndpoint

variable {D}
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : S)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → S}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {e : D.EdgeIndex} {R : D.regions} {a b trim : ℝ} {terminal : Bool}
  {G : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b}
  (E : D.CapGraphEndpoint P region chart caps e R G terminal trim)


noncomputable def outwardRadialVelocity :
    TangentSpace (𝓡 2) (D.edgeFromEndpoint e terminal trim) :=
  -coordinateTriangleVelocity ((caps (D.edgeEndpoint e terminal)).coordinates E.sector)
    (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos) E.chordStartIndex 0

theorem outwardRadialVelocity_eq_firstOuterSpoke (he : E.radialEdge = 2) :
    E.outwardRadialVelocity = (caps (D.edgeEndpoint e terminal)).firstOuterSpoke E.sector.1 := by
  dsimp only [TangentSpace]
  unfold outwardRadialVelocity
  have hi := congrArg (fun k : Fin 3 =>
    (coordinateTriangleVelocity ((caps (D.edgeEndpoint e terminal)).coordinates E.sector)
      (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos) k 0 :
        EuclideanSpace ℝ (Fin 2))) (show E.chordStartIndex = 1 by simp [chordStartIndex, he])
  exact congrArg Neg.neg (hi.trans ((caps _).first_outer_inward_velocity_eq E.sector.1 E.sector.2))

theorem outwardRadialVelocity_eq_secondOuterSpoke (he : E.radialEdge = 1) :
    E.outwardRadialVelocity = (caps (D.edgeEndpoint e terminal)).secondOuterSpoke E.sector.2 := by
  dsimp only [TangentSpace]
  unfold outwardRadialVelocity
  have hi := congrArg (fun k : Fin 3 =>
    (coordinateTriangleVelocity ((caps (D.edgeEndpoint e terminal)).coordinates E.sector)
      (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos) k 0 :
        EuclideanSpace ℝ (Fin 2))) (show E.chordStartIndex = 2 by simp [chordStartIndex, he])
  exact congrArg Neg.neg (hi.trans ((caps _).second_outer_inward_velocity_eq E.sector.2 E.sector.1))

private theorem inward_radial_map (t : ℝ) :
    (caps (D.edgeEndpoint e terminal)).coordinates E.sector
      (AffineMap.lineMap
        (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos E.chordStartIndex)
        (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos 0) t) =
    (((caps (D.edgeEndpoint e terminal)).face E.sector).boundary E.radialEdge).map (1 - t) := by
  rw [(caps _).boundary_map]
  rcases E.radialEdge_valid with he | he
  all_goals
    simp only [he, chordStartIndex]
    rw [← AffineMap.lineMap_apply_one_sub]
    congr 1
    simp [affineChartSegment, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm,
      Fin.succAbove, Fin.lt_def]



theorem edgeFromEndpoint_velocity_pos_smul_outward (htrim : trim ∈ Ioo (0 : ℝ) 1) :
    ∃ a : ℝ, 0 < a ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edgeFromEndpoint e terminal) trim 1 =
        a • E.outwardRadialVelocity := by
  let η := fun t : ℝ => D.edgeFromEndpoint e terminal (trim * (1 - t))
  have hη : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ η :=
    (D.edgeFromEndpoint_contMDiff e terminal).comp
      ((contDiff_const.mul (contDiff_const.sub contDiff_id)).contMDiff :
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => trim * (1 - t)))
  have hparameter (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      trim * (1 - t) ∈ Icc (0 : ℝ) trim := by
    constructor <;> nlinarith [htrim.1, ht.1, ht.2]
  have hφ : HasDerivAt (fun t : ℝ => trim * (1 - t)) (-trim) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_sub 1).const_mul trim
  have hvel := LeviCivitaData.mfderiv_curve_reparam (φ := fun t : ℝ => trim * (1 - t))
    ((D.edgeFromEndpoint_contMDiff e terminal).mdifferentiable (by simp) (trim * (1 - 0))) hφ
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 2) η 0 1 = _ at hvel
  dsimp only [TangentSpace] at hvel ⊢
  have heval := congrArg (fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edgeFromEndpoint e terminal) t 1 : EuclideanSpace ℝ (Fin 2)))
    (show trim * (1 - (0 : ℝ)) = trim by ring)
  have hvel' := hvel.trans (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => (-trim) • v) heval)
  have hηinj : InjOn η (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    have hst := D.edgeFromEndpoint_injective e terminal
      ⟨(hparameter s hs).1, (hparameter s hs).2.trans htrim.2.le⟩
      ⟨(hparameter t ht).1, (hparameter t ht).2.trans htrim.2.le⟩ he
    nlinarith [htrim.1]
  have hηreg : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) η 0 1 ≠ 0 := by
    intro hz
    exact (smul_ne_zero (neg_ne_zero.mpr htrim.1.ne')
      (D.edgeFromEndpoint_velocity_ne_zero e terminal trim)) (hvel'.symm.trans hz)
  have himage : MapsTo η (Icc (0 : ℝ) 1)
      ((fun t : ℝ => (caps (D.edgeEndpoint e terminal)).coordinates E.sector
        (AffineMap.lineMap
          (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos E.chordStartIndex)
          (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos 0) t)) '' Icc (0 : ℝ) 1) := by
    intro t ht
    have hmem : η t ∈ D.edgeFromEndpoint e terminal '' Icc 0 trim :=
      ⟨trim * (1 - t), hparameter t ht, rfl⟩
    rw [← E.radial_image] at hmem
    obtain ⟨u, hu, heq⟩ := hmem
    refine ⟨1 - u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, ?_⟩
    exact (E.inward_radial_map (1 - u)).trans (by simpa only [sub_sub_cancel] using heq)
  have hpoint : η 0 = (caps (D.edgeEndpoint e terminal)).coordinates E.sector
      (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos E.chordStartIndex) := by
    simpa [η] using E.chord_start_eq_tip.symm
  obtain ⟨c, hc, hcap⟩ := regular_curve_velocity_pos_smul_of_coordinate_image
    ((caps (D.edgeEndpoint e terminal)).coordinates E.sector)
    (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos)
    ((caps _).coordinates_smooth E.sector) ((caps _).coordinates_smooth_symm E.sector)
    ((caps _).triangle_subset_source E.sector)
    (show E.chordStartIndex ≠ 0 by unfold chordStartIndex; split_ifs <;> decide)
    (fun t _ => hη.contMDiffAt) hηinj hηreg himage hpoint
  refine ⟨c / trim, div_pos hc htrim.1, ?_⟩
  have heq := hvel'.symm.trans hcap
  have hscale := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => (-trim)⁻¹ • v) heq
  simp [smul_smul, htrim.1.ne', mul_comm, neg_smul] at hscale
  unfold outwardRadialVelocity
  convert hscale using 1 <;> first | rfl | simp [div_eq_mul_inv, smul_neg]

end CapGraphEndpoint

namespace OrientedGraphPiece

variable {D} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S} {a b : ℝ}
  (G : D.OrientedGraphPiece e R C a b)



theorem parameter_deriv_pos {t : ℝ} (ht : t ∈ G.parameter.source) :
    0 < deriv G.parameter t := by
  have hd := (G.parameter_smooth.contDiffAt (G.parameter.open_source.mem_nhds ht)).differentiableAt
    (by simp)
  have hi := (G.parameter_symm_smooth.contDiffAt
    (G.parameter.open_target.mem_nhds (G.parameter.map_source ht))).differentiableAt (by simp)
  have hnonneg := G.parameter_strictMono.monotoneOn.derivWithin_nonneg (x := t)
  rw [hd.derivWithin (G.parameter.open_source.uniqueDiffOn t ht)] at hnonneg
  have heq : (G.parameter.symm ∘ G.parameter) =ᶠ[𝓝 t] id := by
    filter_upwards [G.parameter.open_source.mem_nhds ht] with s hs
    exact G.parameter.left_inv hs
  have hprod : deriv G.parameter.symm (G.parameter t) * deriv G.parameter t = 1 := by
    rw [← deriv_comp t hi hd, heq.deriv_eq, deriv_id]
  apply lt_of_le_of_ne hnonneg
  intro hz
  rw [← hz, mul_zero] at hprod
  norm_num at hprod

private theorem graph_curve_smooth
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    {u : ℝ} (hu : u ∈ G.parameter.target) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun s : ℝ => C (G.frame.symm (s, G.lower s))) u := by
  have hl := G.lower_smooth.contDiffAt (G.parameter.open_target.mem_nhds hu)
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞
      (fun s : ℝ => G.frame.symm (s, G.lower s)) u :=
    (G.frame.symm.contDiff.contDiffAt.comp u (contDiffAt_id.prodMk hl)).contMDiffAt
  exact (hC.contMDiffAt (C.open_source.mem_nhds (G.graph_source u hu))).comp u hline

private theorem edge_velocity_eq_graph_velocity
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    {t : ℝ} (ht : t ∈ G.parameter.source) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map t 1 =
      deriv G.parameter t • mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
        (fun s : ℝ => C (G.frame.symm (s, G.lower s))) (G.parameter t) 1 := by
  have heq : (D.edge e.1 e.2).map =ᶠ[𝓝 t]
      (fun s : ℝ => C (G.frame.symm (s, G.lower s))) ∘ G.parameter := by
    filter_upwards [G.parameter.open_source.mem_nhds ht] with s hs
    exact G.graph_map s hs
  have hd : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map t =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
        ((fun s : ℝ => C (G.frame.symm (s, G.lower s))) ∘ G.parameter) t := heq.mfderiv_eq
  have h := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) => L 1) hd
  exact h.trans (LeviCivitaData.mfderiv_curve_reparam
    ((G.graph_curve_smooth hC (G.parameter.map_source ht)).mdifferentiableAt (by simp))
    ((G.parameter_smooth.contDiffAt (G.parameter.open_source.mem_nhds ht)).differentiableAt
      (by simp)).hasDerivAt)

namespace FixedStripBandFaces

variable {G} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

private theorem bottom_map (i : Fin B.faces.interface.count) (t : ℝ) :
    B.faces.faceCoordinates (i, false)
      (AffineMap.lineMap (B.faces.faceBasis (i, false) 0)
        (B.faces.faceBasis (i, false) 1) t) =
      C (G.frame.symm
        (G.parameter a +
          (B.faces.cut i.castSucc + t * (B.faces.cut i.succ - B.faces.cut i.castSucc)) *
            (G.parameter b - G.parameter a),
        G.lower (G.parameter a +
          (B.faces.cut i.castSucc + t * (B.faces.cut i.succ - B.faces.cut i.castSucc)) *
            (G.parameter b - G.parameter a)))) := by
  have h := (B.faces.pair i).lower_chart_map
    (B.faces.interface.pieceCoordinates B.faces.open_domain B.faces.smooth_lower i).parameter.open_target
    contDiffOn_const
    ((B.faces.interface.pieceCoordinates B.faces.open_domain B.faces.smooth_lower i).smooth_upperGraph
      B.faces.smooth_lower) t
  rw [coordinateTriangle_first_map, (B.faces.pair i).lower_edge] at h
  change B.faces.faceCoordinates (i, false)
      (AffineMap.lineMap (B.faces.faceBasis (i, false) 0)
        (B.faces.faceBasis (i, false) 1) t) =
      B.faces.coordinates (collarParameterEquiv.symm
        (B.faces.cut i.castSucc + t * (B.faces.cut i.succ - B.faces.cut i.castSucc), 0)) at h
  rw [h, B.coordinates_eq, G.strip_axis]



theorem first_bottom_velocity_pos_smul_edge (hab : a < b)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source) :
    ∃ c : ℝ, 0 < c ∧
      coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.firstCell, false))
        (B.faces.faceBasis (B.faces.firstCell, false)) 0 1 =
      c • mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map a 1 := by
  let w := B.faces.cut B.faces.firstCell.succ - B.faces.cut B.faces.firstCell.castSucc
  let d := G.parameter b - G.parameter a
  have hw : 0 < w := sub_pos.mpr (B.faces.cut_strictMono Fin.castSucc_lt_succ)
  have hd : 0 < d := sub_pos.mpr (G.parameter_lt hab)
  have ha := G.interval_source (left_mem_Icc.mpr hab.le)
  have hp := G.parameter_deriv_pos ha
  have hparam : HasDerivAt (fun t : ℝ => G.parameter a + t * (w * d)) (w * d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w * d)).const_add (G.parameter a)
  have hcurve : (fun t : ℝ => B.faces.faceCoordinates (B.faces.firstCell, false)
      (AffineMap.lineMap (B.faces.faceBasis (B.faces.firstCell, false) 0)
        (B.faces.faceBasis (B.faces.firstCell, false) 1) t)) =
      (fun s : ℝ => C (G.frame.symm (s, G.lower s))) ∘
        (fun t : ℝ => G.parameter a + t * (w * d)) := by
    funext t
    rw [B.bottom_map]
    have hz : B.faces.firstCell.castSucc = 0 := rfl
    simp only [hz, B.faces.cut_first, zero_add, Function.comp_apply, w, d, mul_assoc]
  have hv := LeviCivitaData.mfderiv_curve_reparam
    (φ := fun t : ℝ => G.parameter a + t * (w * d))
    (by simpa only [zero_mul, add_zero] using
      (G.graph_curve_smooth hC (G.parameter.map_source ha)).mdifferentiableAt (by simp)) hparam
  have he := G.edge_velocity_eq_graph_velocity hC ha
  refine ⟨w * d / deriv G.parameter a, div_pos (mul_pos hw hd) hp, ?_⟩
  dsimp only [TangentSpace] at hv he ⊢
  unfold coordinateTriangleVelocity
  rw [hcurve]
  have hpoint := congrArg (fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s : ℝ => C (G.frame.symm (s, G.lower s))) t 1 :
      EuclideanSpace ℝ (Fin 2))) (show G.parameter a + 0 * (w * d) = G.parameter a by ring)
  have hv' := hv.trans (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => (w * d) • v) hpoint)
  exact hv'.trans (by rw [he, smul_smul, div_mul_cancel₀ _ hp.ne']; congr 2)



theorem last_bottom_velocity_pos_smul_edge (hab : a < b)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source) :
    ∃ c : ℝ, 0 < c ∧
      coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.lastCell, false))
        (B.faces.faceBasis (B.faces.lastCell, false)) 1 0 =
      c • (-mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map b 1) := by
  let w := B.faces.cut B.faces.lastCell.succ - B.faces.cut B.faces.lastCell.castSucc
  let d := G.parameter b - G.parameter a
  have hw : 0 < w := sub_pos.mpr (B.faces.cut_strictMono Fin.castSucc_lt_succ)
  have hd : 0 < d := sub_pos.mpr (G.parameter_lt hab)
  have hb := G.interval_source (right_mem_Icc.mpr hab.le)
  have hp := G.parameter_deriv_pos hb
  have hparam : HasDerivAt (fun t : ℝ => G.parameter b - t * (w * d)) (-(w * d)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w * d)).const_sub (G.parameter b)
  have hcurve : (fun t : ℝ => B.faces.faceCoordinates (B.faces.lastCell, false)
      (AffineMap.lineMap (B.faces.faceBasis (B.faces.lastCell, false) 1)
        (B.faces.faceBasis (B.faces.lastCell, false) 0) t)) =
      (fun s : ℝ => C (G.frame.symm (s, G.lower s))) ∘
        (fun t : ℝ => G.parameter b - t * (w * d)) := by
    funext t
    rw [← AffineMap.lineMap_apply_one_sub, B.bottom_map]
    have hlast : B.faces.lastCell.succ = Fin.last B.faces.interface.count := by
      apply Fin.ext
      have hn := B.faces.interface.count_pos
      simp only [ObliqueBandFaces.lastCell, Fin.val_succ, Fin.val_last]
      omega
    have heq : G.parameter a +
        (B.faces.cut B.faces.lastCell.castSucc +
          (1 - t) * (B.faces.cut B.faces.lastCell.succ - B.faces.cut B.faces.lastCell.castSucc)) *
            (G.parameter b - G.parameter a) = G.parameter b - t * (w * d) := by
      dsimp only [w, d]
      rw [hlast, B.faces.cut_last]
      ring
    rw [heq]
    rfl
  have hv := LeviCivitaData.mfderiv_curve_reparam
    (φ := fun t : ℝ => G.parameter b - t * (w * d))
    (by simpa only [zero_mul, sub_zero] using
      (G.graph_curve_smooth hC (G.parameter.map_source hb)).mdifferentiableAt (by simp)) hparam
  have he := G.edge_velocity_eq_graph_velocity hC hb
  refine ⟨w * d / deriv G.parameter b, div_pos (mul_pos hw hd) hp, ?_⟩
  dsimp only [TangentSpace] at hv he ⊢
  unfold coordinateTriangleVelocity
  rw [hcurve]
  have hpoint := congrArg (fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s : ℝ => C (G.frame.symm (s, G.lower s))) t 1 :
      EuclideanSpace ℝ (Fin 2))) (show G.parameter b - 0 * (w * d) = G.parameter b by ring)
  have hv' := hv.trans (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => (-(w * d)) • v) hpoint)
  exact hv'.trans (by rw [he, smul_neg, smul_smul, div_mul_cancel₀ _ hp.ne', neg_smul]; congr 2)

end FixedStripBandFaces
end OrientedGraphPiece

namespace OrientedEdgeGraphSubdivision.CutChain

variable {D : FiniteChartRegionDecomposition (M := S)}
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : S)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → S}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {cut : D.EdgeIndex → Bool → ℝ} {e : D.EdgeIndex} {R : D.regions}
  {Q : D.OrientedEdgeGraphSubdivision e R
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (cut e false) (1 - cut e true)}
  (L : D.CapGraphEndpoint P region chart caps e R (Q.piece Q.firstPiece) false (cut e false))
  (T : D.CapGraphEndpoint P region chart caps e R (Q.piece Q.lastPiece) true (cut e true))
  (K : Q.CutChain L.direction T.direction)
  {r δ : ℝ}


theorem first_cap_bottom_velocity_pos_smul
    (B : (Q.piece Q.firstPiece).FixedStripBandFaces (K.graphCuts Q.firstPiece) δ r r) :
    ∃ a : ℝ, 0 < a ∧
      coordinateTriangleVelocity
        (B.faces.faceCoordinates (B.faces.firstCell, false))
        (B.faces.faceBasis (B.faces.firstCell, false)) 0 1 = a • L.outwardRadialVelocity := by
  have htrim : cut e false ∈ Ioo (0 : ℝ) 1 := by
    simpa only [Q.cut_first] using Q.cut_mem 0
  obtain ⟨a, ha, he⟩ := B.first_bottom_velocity_pos_smul_edge (Q.cut_lt Q.firstPiece)
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
  obtain ⟨b, hb, hc⟩ := L.edgeFromEndpoint_velocity_pos_smul_outward htrim
  dsimp only [TangentSpace] at he hc ⊢
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map (cut e false) 1 = _ at hc
  have hp := congrArg (fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map t 1 : EuclideanSpace ℝ (Fin 2)))
    (show Q.cut Q.firstPiece.castSucc = cut e false by rw [Q.firstPiece_castSucc, Q.cut_first])
  refine ⟨a * b, mul_pos ha hb, ?_⟩
  exact he.trans ((congrArg (fun v : EuclideanSpace ℝ (Fin 2) => a • v) (hp.trans hc)).trans
    (smul_smul a b _))



theorem last_cap_bottom_velocity_pos_smul
    (B : (Q.piece Q.lastPiece).FixedStripBandFaces (K.graphCuts Q.lastPiece) δ r r) :
    ∃ a : ℝ, 0 < a ∧
      coordinateTriangleVelocity
        (B.faces.faceCoordinates (B.faces.lastCell, false))
        (B.faces.faceBasis (B.faces.lastCell, false)) 1 0 = a • T.outwardRadialVelocity := by
  have ht := Q.cut_mem (Fin.last Q.count)
  rw [Q.cut_last] at ht
  have htrim : cut e true ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨a, ha, he⟩ := B.last_bottom_velocity_pos_smul_edge (Q.cut_lt Q.lastPiece)
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
  obtain ⟨b, hb, hc⟩ := T.edgeFromEndpoint_velocity_pos_smul_outward htrim
  dsimp only [TangentSpace] at he hc ⊢
  have hc' := (D.edgeFromEndpoint_terminal_velocity e (cut e true)).symm.trans hc
  have hp := congrArg (fun t : ℝ =>
    (-mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map t 1 : EuclideanSpace ℝ (Fin 2)))
    (show Q.cut Q.lastPiece.succ = 1 - cut e true by rw [Q.lastPiece_succ, Q.cut_last])
  refine ⟨a * b, mul_pos ha hb, ?_⟩
  exact he.trans ((congrArg (fun v : EuclideanSpace ℝ (Fin 2) => a • v) (hp.trans hc')).trans
    (smul_smul a b _))



theorem first_cap_band_refined_contribution (g : RiemannianMetric 2 S)
    (B : (Q.piece Q.firstPiece).FixedStripBandFaces (K.graphCuts Q.firstPiece) δ r r)
    (hr : r ≤ 1)
    (lines : (Fin B.faces.interface.count × Bool) →
      List (EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)) :
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (D.edgeFromEndpoint e false (cut e false))) =
      g.cornerAngle (D.edgeFromEndpoint e false (cut e false))
        L.outwardRadialVelocity L.chordVelocity := by
  have hcoord := linearGraphCoordinates_contMDiff
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (Q.piece Q.firstPiece).frame
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
  have hpoint : B.faces.vertex (0, false) = D.edgeFromEndpoint e false (cut e false) := by
    have h := B.left_endpoint_coordinate_start (Q.cut_lt Q.firstPiece).le
    rw [B.faces.face_corner_eq_vertex] at h
    simpa [ObliqueBandFaces.cornerVertexIndex, ObliqueBandFaces.firstCell,
      Q.firstPiece_castSucc, Q.cut_first, edgeFromEndpoint] using h
  have hfan := B.faces.first_bottom_refined_vertex_fan g hcoord.1 hcoord.2 lines
  obtain ⟨a, ha, hb⟩ := K.first_cap_bottom_velocity_pos_smul L T B
  obtain ⟨b, hbpos, hc⟩ := K.first_cap_cut_velocity_pos_smul L T B hr
  dsimp only [TangentSpace] at hb hc ⊢
  rw [hpoint] at hfan
  rw [hfan, hb, hc, g.cornerAngle_smul_pos_left _ _ _ ha,
    g.cornerAngle_smul_pos_right _ _ _ hbpos]



theorem last_cap_band_refined_contribution (g : RiemannianMetric 2 S)
    (B : (Q.piece Q.lastPiece).FixedStripBandFaces (K.graphCuts Q.lastPiece) δ r r)
    (hr : r ≤ 1)
    (lines : (Fin B.faces.interface.count × Bool) →
      List (EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)) :
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (D.edgeFromEndpoint e true (cut e true))) =
      g.cornerAngle (D.edgeFromEndpoint e true (cut e true))
        T.outwardRadialVelocity T.chordVelocity := by
  have hcoord := linearGraphCoordinates_contMDiff
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (Q.piece Q.lastPiece).frame
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
  have hpoint : B.faces.vertex (Fin.last B.faces.interface.count, false) =
      D.edgeFromEndpoint e true (cut e true) := by
    have h := B.right_endpoint_coordinate_start (Q.cut_lt Q.lastPiece).le
    rw [B.faces.face_corner_eq_vertex] at h
    change B.faces.vertex (B.faces.lastCell.succ, false) = _ at h
    have hl : B.faces.lastCell.succ = Fin.last B.faces.interface.count := by
      apply Fin.ext
      have hn := B.faces.interface.count_pos
      simp only [ObliqueBandFaces.lastCell, Fin.val_succ, Fin.val_last]
      omega
    rw [hl] at h
    simpa only [Q.lastPiece_succ, Q.cut_last, edgeFromEndpoint, if_true] using h
  have hfan := B.faces.last_bottom_refined_vertex_fan g hcoord.1 hcoord.2 lines
  obtain ⟨a, ha, hb⟩ := K.last_cap_bottom_velocity_pos_smul L T B
  obtain ⟨b, hbpos, hc⟩ := K.last_cap_cut_velocity_pos_smul L T B hr
  dsimp only [TangentSpace] at hb hc ⊢
  rw [hpoint] at hfan
  rw [hfan, hb, hc, g.cornerAngle_smul_pos_left _ _ _ ha,
    g.cornerAngle_smul_pos_right _ _ _ hbpos]

end OrientedEdgeGraphSubdivision.CutChain
end FiniteChartRegionDecomposition

end PoincareConjecture.Topology.Surface
