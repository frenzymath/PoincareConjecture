import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.AmbientSectorCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.RefinedFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.EndpointRays

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles
open Poincare.Topology.Plane.Curves

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in

theorem coordinateTriangleVelocity_pos_smul_of_chart_segment
    (F C : OpenPartialHomeomorph Plane S) (b : AffineBasis (Fin 3) ℝ Plane)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {i j : Fin 3} (hij : i ≠ j) {p q : Plane} (hpq : p ≠ q)
    (hseg : segment ℝ p q ⊆ C.source)
    (himage : (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) '' Icc (0 : ℝ) 1 ⊆
      C '' segment ℝ p q)
    (hpoint : F (b i) = C p) :
    ∃ r : ℝ, 0 < r ∧ coordinateTriangleVelocity F b i j =
      r • (mfderiv (𝓡 2) (𝓡 2) C p (q - p)) := by
  let γ : ℝ → S := fun t => C (AffineMap.lineMap p q t)
  let η : ℝ → S := fun t => F (AffineMap.lineMap (b i) (b j) t)
  let e := C.symm.trans collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph
  let p' := collarParameterEquiv p
  let v' := collarParameterEquiv (q - p)
  have hp : p ∈ C.source := hseg (left_mem_segment ℝ p q)
  have hv : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hmap (t : ℝ) : C (p + t • (q - p)) = γ t := by
    simp only [γ, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
  have htarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p + t • (q - p) ∈ C.source := by
    apply hseg
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, by simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]⟩
  have hη (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ η t :=
    (coordinateTriangle_side_velocity F b hF hFi hb i j ht).1
  have hmaps : MapsTo η (Icc (0 : ℝ) 1)
      ((fun t : ℝ => C (p + t • (q - p))) '' Icc (0 : ℝ) 1) := by
    intro t ht
    obtain ⟨z, hz, he⟩ := himage (mem_image_of_mem η ht)
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    refine ⟨s, hs, ?_⟩
    change C (p + s • (q - p)) = η t
    rw [hmap]
    exact he
  have he_smooth : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source :=
    collarParameterEquiv.contDiff.contMDiff.comp_contMDiffOn
      (hCi.mono (fun _ hx => hx.1))
  have he_map (t : ℝ) : e.symm (p' + t • v') = γ t := by
    change C (collarParameterEquiv.symm (collarParameterEquiv p +
      t • collarParameterEquiv (q - p))) = γ t
    rw [map_add, map_smul, collarParameterEquiv.symm_apply_apply,
      collarParameterEquiv.symm_apply_apply, hmap]
  have he_target (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p' + t • v' ∈ e.target := by
    refine ⟨mem_univ _, ?_⟩
    change collarParameterEquiv.symm (collarParameterEquiv p +
      t • collarParameterEquiv (q - p)) ∈ C.source
    simpa only [map_add, map_smul, collarParameterEquiv.symm_apply_apply] using htarget t ht
  have hv' : v' ≠ 0 := by
    exact fun h => hv (collarParameterEquiv.injective (h.trans (map_zero _).symm))
  obtain ⟨φ, hφ, hφmaps, heq, huniq⟩ := LeviCivitaData.exists_smooth_chart_edge_parameter
    e he_smooth p' v' hv' he_target hη (by simpa only [he_map, hmap] using hmaps)
  have heq' : EqOn η (γ ∘ φ) (Icc (0 : ℝ) 1) := by
    intro t ht
    simpa only [Function.comp_apply, he_map] using heq t ht
  have hzero : φ 0 = 0 := by
    apply huniq 0 (by simp) 0 (by simp)
    rw [he_map]
    simpa only [γ, η, AffineMap.lineMap_apply_zero] using hpoint
  have hηinj : InjOn η (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    apply AffineMap.lineMap_injective ℝ (b.ind.injective.ne hij)
    apply F.injOn
      (hb ((convex_convexHull ℝ (range b)).lineMap_mem
        (subset_convexHull ℝ _ (mem_range_self i))
        (subset_convexHull ℝ _ (mem_range_self j)) hs))
      (hb ((convex_convexHull ℝ (range b)).lineMap_mem
        (subset_convexHull ℝ _ (mem_range_self i))
        (subset_convexHull ℝ _ (mem_range_self j)) ht)) he
  have hφinj : InjOn φ (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    apply hηinj hs ht
    rw [heq' hs, heq' ht, Function.comp_apply, Function.comp_apply, he]
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn φ (Icc (0 : ℝ) 1) := by
    rcases hcont.strictMonoOn_of_injOn_Icc' zero_le_one hφinj with hm | hm
    · exact hm
    · have hn := hm (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1) zero_lt_one
      have hp := (hφmaps (by simp : (1 : ℝ) ∈ Icc 0 1)).1
      rw [hzero] at hn
      exact (not_lt_of_ge hp hn).elim
  have hdiff : DifferentiableAt ℝ φ 0 := (hφ 0 (by simp)).differentiableAt (by simp)
  have hnonneg : 0 ≤ deriv φ 0 := by
    have h := hmono.monotoneOn.derivWithin_nonneg (x := 0)
    rwa [hdiff.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 (by simp))] at h
  have hCp := (hC.contMDiffAt (C.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  have hd : HasDerivAt (fun t : ℝ => AffineMap.lineMap p q t) (q - p) 0 := by
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, one_smul, id_eq]
      using ((hasDerivAt_id (0 : ℝ)).smul_const (q - p)).add_const p
  have hCp' : MDifferentiableAt (𝓡 2) (𝓡 2) C (AffineMap.lineMap p q (0 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero] using hCp
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ 0 :=
    hCp'.comp 0 hd.differentiableAt.mdifferentiableAt
  have hvelocity := mfderiv_curve_reparam_zero_of_eqOn hγ
    ((hη 0 (by simp)).mdifferentiableAt (by simp)) hdiff hzero heq'
  have hne : deriv φ 0 ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hvelocity
    exact coordinateTriangleVelocity_ne_zero F b hF hFi hb hij hvelocity
  refine ⟨deriv φ 0, lt_of_le_of_ne hnonneg hne.symm, ?_⟩
  have h := congrArg (fun L => L 1) (mfderiv_comp (0 : ℝ)
    (by simpa using hCp) hd.differentiableAt.mdifferentiableAt)
  dsimp only [TangentSpace] at h hvelocity ⊢
  simp only [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
  rw [AffineMap.lineMap_apply_zero] at h
  exact hvelocity.trans (congrArg (fun v => deriv φ 0 • v) h)

theorem affineBasis_direction_expansion (c : AffineBasis (Fin 3) ℝ Plane) (v : Plane) :
    v = (c.coord 1).linear v • (c 1 - c 0) +
      (c.coord 2).linear v • (c 2 - c 0) := by
  have hc := c.linear_combination_coord_eq_self (v + c 0)
  have hs := c.sum_coord_apply_eq_one (v + c 0)
  have he (k : Fin 3) : c.coord k (v + c 0) = (c.coord k).linear v + c.coord k (c 0) :=
    (c.coord k).map_vadd (c 0) v
  simp only [Fin.sum_univ_three, he, AffineBasis.coord_apply,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    if_true, if_false, add_zero] at hc hs
  have hz : (c.coord 0).linear v + 1 = 1 - (c.coord 1).linear v - (c.coord 2).linear v := by
    linarith
  rw [hz] at hc
  apply add_right_cancel (b := c 0)
  rw [← hc]
  module

theorem cornerAngle_split_of_positive_sector_coordinates
    (g : RiemannianMetric 2 S) (x : S) (c : AffineBasis (Fin 3) ℝ Plane)
    (L : Plane →L[ℝ] TangentSpace (𝓡 2) x) (v : Plane)
    (h1 : 0 < (c.coord 1).linear v) (h2 : 0 < (c.coord 2).linear v)
    (hne : L v ≠ 0) :
    g.cornerAngle x (L (c 1 - c 0)) (L (c 2 - c 0)) =
      g.cornerAngle x (L v) (L (c 1 - c 0)) +
      g.cornerAngle x (L v) (L (c 2 - c 0)) := by
  have he : L v = (c.coord 1).linear v • L (c 1 - c 0) +
      (c.coord 2).linear v • L (c 2 - c 0) := by
    conv_lhs => rw [affineBasis_direction_expansion c v, map_add, map_smul, map_smul]
  have h := g.cornerAngle_split_of_nonneg_combination x (L (c 1 - c 0))
    (L (c 2 - c 0)) h1.le h2.le (he ▸ hne)
  rw [← he, g.cornerAngle_comm x (L (c 1 - c 0)) (L v)] at h
  exact h

namespace ObliqueBandFaces

variable {F : OpenPartialHomeomorph Plane S} {lo : ℝ → ℝ}
  {a b ua wa ub wb ra rb : ℝ} (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

theorem topLineFunctional_cut_fderiv_pos (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) :
    0 < (B.topLineFunctional i).linear (collarParameterEquiv.symm
      (fderiv ℝ (B.cuts.coordinates B.open_domain B.smooth_lower)
        (t, B.upperGraph i t) (0, 1))) := by
  let Q := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  let η := B.upperGraph i t
  let x := Q.parameter.symm t
  let f : (ℝ × ℝ) → ℝ := fun q =>
    (B.cuts.coordinates B.open_domain B.smooth_lower q).2 -
      B.interface.piece i (B.cuts.coordinates B.open_domain B.smooth_lower q).1
  have htQ := Q.parameter_mem_target ht
  have hxcell := Q.inverse_mem_cell ht
  have hz : η ∈ Ioo (-B.cuts.radius) B.cuts.radius :=
    (Q.source_subset (Q.parameter.map_target htQ)).2
  have hxdom : x ∈ B.domain := (Q.source_subset (Q.parameter.map_target htQ)).1
  have hsource : (t, η) ∈ (B.cuts.coordinates B.open_domain B.smooth_lower).source :=
    Q.band_subset_coordinates_source B.open_domain B.smooth_lower
      ⟨ht, (Q.upperGraph_bounds ht).1.le, le_rfl⟩
  have hpiece : ContDiff ℝ ∞ (B.interface.piece i) := by
    rw [(B.interface.piece i).decomp]
    exact (B.interface.piece i).linear.toContinuousLinearMap.contDiff.add contDiff_const
  have hc := (B.cuts.smooth_coordinates B.open_domain B.smooth_lower).contDiffAt
    ((B.cuts.coordinates B.open_domain B.smooth_lower).open_source.mem_nhds hsource)
  have hfc : ContDiffAt ℝ ∞ f (t, η) := hc.snd.sub (hpiece.contDiffAt.comp _ hc.fst)
  have hA := ((B.cuts.smooth_A η hz).contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt
    (by simp)
  have hB := ((B.cuts.smooth_B η hz).contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt
    (by simp)
  have hlo := ((B.smooth_lower x hxdom).contDiffAt (B.open_domain.mem_nhds hxdom)).differentiableAt
    (by simp)
  have hmap := Q.strip_upperGraph_eq ht
  have hx : B.cuts.A η + t * (B.cuts.B η - B.cuts.A η) = x := congrArg Prod.fst hmap
  let v := deriv B.cuts.A η + t * (deriv B.cuts.B η - deriv B.cuts.A η)
  have hhorizontal : HasDerivAt
      (fun z => B.cuts.A z + t * (B.cuts.B z - B.cuts.A z)) v η :=
    hA.hasDerivAt.add ((hB.hasDerivAt.sub hA.hasDerivAt).const_mul t)
  have hlo' : HasDerivAt lo (deriv lo x)
      (B.cuts.A η + t * (B.cuts.B η - B.cuts.A η)) := hx.symm ▸ hlo.hasDerivAt
  have hd : HasDerivAt (fun z => f (t, z))
      ((deriv lo x - (B.interface.piece i).linear 1) * v + 1) η := by
    convert! ((hlo'.comp η hhorizontal).add (hasDerivAt_id η)).sub
      ((B.interface.piece i).hasDerivAt.comp η hhorizontal) using 1
    · funext z
      simp [f, B.cuts.coordinates_apply, obliqueStripMap]
    · ring
  have hfderiv : fderiv ℝ f (t, η) (0, 1) =
      (deriv lo x - (B.interface.piece i).linear 1) * v + 1 := by
    have hd' := (hfc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt η
      ((hasDerivAt_const η t).prodMk (hasDerivAt_id η))
    exact hd'.unique hd
  have hpositive : 0 < fderiv ℝ f (t, η) (0, 1) := by
    rw [hfderiv]
    have hp := B.interface.projection_deriv_pos i x hxcell
    have hg : 0 < B.cuts.B η - B.cuts.A η := sub_pos.mpr (B.cuts.separated η hz)
    change 0 < obliqueProjectionDerivative B.cuts.A B.cuts.B
      (x, (η, (B.interface.piece i).linear 1 - deriv lo x)) at hp
    unfold obliqueProjectionDerivative at hp
    have hn := (div_pos_iff_of_pos_right (sq_pos_of_pos hg)).mp hp
    have hid :
        (1 - deriv B.cuts.A η * ((B.interface.piece i).linear 1 - deriv lo x)) *
            (B.cuts.B η - B.cuts.A η) -
          (x - B.cuts.A η) * ((deriv B.cuts.B η - deriv B.cuts.A η) *
            ((B.interface.piece i).linear 1 - deriv lo x)) =
        (B.cuts.B η - B.cuts.A η) *
          ((deriv lo x - (B.interface.piece i).linear 1) * v + 1) := by
      rw [← hx]
      dsimp [v]
      ring
    rw [hid] at hn
    exact (mul_pos_iff_of_pos_left hg).mp hn
  let l : (ℝ × ℝ) →ᵃ[ℝ] ℝ := (B.topLineFunctional i).comp
    collarParameterEquiv.symm.toContinuousLinearMap.toLinearMap.toAffineMap
  let lc : (ℝ × ℝ) →ᴬ[ℝ] ℝ := ⟨l, l.continuous_of_finiteDimensional⟩
  have he : f = l ∘ B.cuts.coordinates B.open_domain B.smooth_lower := by
    funext z
    simp [f, l, topLineFunctional_apply, topLineExcess]
  rw [he] at hpositive
  change 0 < fderiv ℝ (lc ∘ B.cuts.coordinates B.open_domain B.smooth_lower) (t, η) (0, 1) at hpositive
  rw [fderiv_comp _ lc.differentiableAt
    (hc.differentiableAt (by simp)), lc.fderiv] at hpositive
  exact hpositive

end ObliqueBandFaces

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {D : FiniteChartRegionDecomposition (M := S)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane S} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

theorem chartTopVertex_ne (i : Fin B.faces.interface.count) :
    B.chartTopVertex i.castSucc ≠ B.chartTopVertex i.succ := by
  intro he
  have hh := congrArg (fun z : Plane => (G.frame z).1) he
  simp only [chartTopVertex, G.frame.apply_symm_apply] at hh
  exact (B.faces.interface.cut_strictMono Fin.castSucc_lt_succ).ne hh

theorem cut_top_eq_chartTopVertex (i : Fin B.faces.interface.count)
    (k : Fin (B.faces.interface.count + 1)) (hk : k = i.castSucc ∨ k = i.succ) :
    G.frame.symm (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
      (B.faces.cut k, B.faces.interface.height k)) = B.chartTopVertex k := by
  let Q := B.faces.interface.pieceCoordinates B.faces.open_domain B.faces.smooth_lower i
  have ht : B.faces.cut k ∈ Icc (B.faces.cut i.castSucc) (B.faces.cut i.succ) := by
    rcases hk with rfl | rfl
    · exact left_mem_Icc.mpr (B.faces.cut_strictMono Fin.castSucc_lt_succ).le
    · exact right_mem_Icc.mpr (B.faces.cut_strictMono Fin.castSucc_lt_succ).le
  have hparam : Q.parameter.symm (B.faces.cut k) = B.faces.interface.cut k := by
    have h := Q.parameter.left_inv (Q.source_contains (show
        B.faces.interface.cut k ∈ Icc (B.faces.interface.cut i.castSucc)
          (B.faces.interface.cut i.succ) from by
      rcases hk with rfl | rfl
      · exact left_mem_Icc.mpr (B.faces.interface.cut_strictMono Fin.castSucc_lt_succ).le
      · exact right_mem_Icc.mpr (B.faces.interface.cut_strictMono Fin.castSucc_lt_succ).le))
    rw [Q.map_eq] at h
    rcases hk with rfl | rfl
    · rwa [(B.faces.interface.projection_endpoints i).1] at h
    · rwa [(B.faces.interface.projection_endpoints i).2] at h
  have hh : B.faces.upperGraph i (B.faces.cut k) = B.faces.interface.height k := by
    rcases hk with rfl | rfl
    · exact (B.faces.upperGraph_endpoints i).1
    · exact (B.faces.upperGraph_endpoints i).2
  have hp : B.faces.interface.piece i (B.faces.interface.cut k) =
      G.lower (B.faces.interface.cut k) + B.faces.interface.height k := by
    rcases hk with rfl | rfl
    · exact (B.faces.interface.piece_endpoints i).1
    · exact (B.faces.interface.piece_endpoints i).2
  have hmap := Q.strip_upperGraph_eq ht
  change obliqueStripMap B.faces.cuts.A B.faces.cuts.B G.lower
    (B.faces.cut k, B.faces.upperGraph i (B.faces.cut k)) = _ at hmap
  rw [hh, hparam, hp] at hmap
  rw [B.faces.cuts.coordinates_apply, hmap]
  rfl

theorem vertex_top_eq_chartTopVertex (i : Fin B.faces.interface.count)
    (k : Fin (B.faces.interface.count + 1)) (hk : k = i.castSucc ∨ k = i.succ) :
    B.faces.vertex (k, true) = C (B.chartTopVertex k) := by
  simp only [ObliqueBandFaces.vertex, if_true, B.faces.coordinates_pair_apply,
    linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply,
    B.cut_top_eq_chartTopVertex i k hk]

noncomputable def ambientOutwardDirection (k : Fin (B.faces.interface.count + 1)) : Plane :=
  G.frame.symm (fderiv ℝ (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower)
    (B.faces.cut k, B.faces.interface.height k) (0, 1))

theorem ambientTopFunctional_outward_pos (i : Fin B.faces.interface.count)
    (k : Fin (B.faces.interface.count + 1)) (hk : k = i.castSucc ∨ k = i.succ) :
    0 < (B.ambientTopFunctional i).linear (B.ambientOutwardDirection k) := by
  have ht : B.faces.cut k ∈ Icc (B.faces.cut i.castSucc) (B.faces.cut i.succ) := by
    rcases hk with rfl | rfl
    · exact left_mem_Icc.mpr (B.faces.cut_strictMono Fin.castSucc_lt_succ).le
    · exact right_mem_Icc.mpr (B.faces.cut_strictMono Fin.castSucc_lt_succ).le
  have hh : B.faces.upperGraph i (B.faces.cut k) = B.faces.interface.height k := by
    rcases hk with rfl | rfl
    · exact (B.faces.upperGraph_endpoints i).1
    · exact (B.faces.upperGraph_endpoints i).2
  have h := B.faces.topLineFunctional_cut_fderiv_pos i ht
  rw [hh] at h
  simpa [ambientTopFunctional, ambientOutwardDirection] using h

theorem topOutwardRay_eq_chart_differential
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i : Fin B.faces.interface.count) :
    B.faces.topOutwardRay i = B.faces.interface.height i.succ •
      mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ) (B.ambientOutwardDirection i.succ) := by
  let Q := B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
  let h := B.faces.interface.height i.succ
  let t := B.faces.cut i.succ
  let β : ℝ → Plane := fun s => G.frame.symm (Q (t, s * h))
  have ht : t ∈ Icc (B.faces.cut i.castSucc) (B.faces.cut i.succ) :=
    right_mem_Icc.mpr (B.faces.cut_strictMono Fin.castSucc_lt_succ).le
  have hsource : (t, h) ∈ Q.source := by
    have hs := (B.faces.interface.pieceCoordinates B.faces.open_domain B.faces.smooth_lower i).band_subset_coordinates_source
      B.faces.open_domain B.faces.smooth_lower
        (show (t, B.faces.upperGraph i t) ∈ {q : ℝ × ℝ |
          q.1 ∈ Icc (B.faces.cut i.castSucc) (B.faces.cut i.succ) ∧ 0 ≤ q.2 ∧
            q.2 ≤ B.faces.upperGraph i q.1} from
          ⟨ht, ((B.faces.interface.pieceCoordinates B.faces.open_domain B.faces.smooth_lower i).upperGraph_bounds ht).1.le,
            le_rfl⟩)
    simpa only [t, (B.faces.upperGraph_endpoints i).2] using hs
  have hQ := ((B.faces.cuts.smooth_coordinates B.faces.open_domain B.faces.smooth_lower).contDiffAt
    (Q.open_source.mem_nhds hsource)).differentiableAt (by simp)
  have hinput : HasDerivAt (fun s : ℝ => (t, s * h)) (0, h) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) t).prodMk ((hasDerivAt_id (1 : ℝ)).mul_const h)
  have hQ' : HasFDerivAt Q (fderiv ℝ Q (t, h)) (t, (1 : ℝ) * h) := by
    simpa only [one_mul] using hQ.hasFDerivAt
  have hβ := G.frame.symm.hasFDerivAt.comp_hasDerivAt (1 : ℝ)
    (hQ'.comp_hasDerivAt 1 hinput)
  have hβ' : HasDerivAt β (h • B.ambientOutwardDirection i.succ) 1 := by
    convert! hβ using 1
    symm
    change G.frame.symm (fderiv ℝ Q (t, h) (0, h)) = _
    have hh : ((0 : ℝ), h) = h • ((0 : ℝ), 1) := by ext <;> simp
    rw [hh, map_smul, map_smul]
    rfl
  have hpoint : β 1 = B.chartTopVertex i.succ := by
    simpa only [β, one_mul] using B.cut_top_eq_chartTopVertex i i.succ (Or.inr rfl)
  have hp : B.chartTopVertex i.succ ∈ C.source :=
    B.chartTopSegment_subset_source i (right_mem_segment ℝ _ _)
  have hCp := (hC.contMDiffAt (C.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  have hCp' : MDifferentiableAt (𝓡 2) (𝓡 2) C (β 1) := hpoint.symm ▸ hCp
  have hd := congrArg (fun L => L 1) (mfderiv_comp (1 : ℝ) hCp'
    hβ'.differentiableAt.mdifferentiableAt)
  dsimp only [TangentSpace] at hd ⊢
  simp only [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, hβ'.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, map_smul] at hd
  have hd' : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (C ∘ β) 1 1 =
      h • mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
        (B.ambientOutwardDirection i.succ) := by
    exact hd.trans (congrArg (fun z : Plane => h •
      (mfderiv (𝓡 2) (𝓡 2) C z (B.ambientOutwardDirection i.succ) : Plane)) hpoint)
  rw [B.faces.topOutwardRay_eq_cut_velocity
    (linearGraphCoordinates_contMDiff C G.frame hC hCi).1]
  convert! hd' using 1

theorem topRightChord_pos_smul_chart_differential
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i : Fin B.faces.interface.count) :
    ∃ r : ℝ, 0 < r ∧ B.faces.topRightChord i =
      r • mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.castSucc)
        (B.chartTopVertex i.succ - B.chartTopVertex i.castSucc) := by
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  apply coordinateTriangleVelocity_pos_smul_of_chart_segment
    (B.faces.faceCoordinates (i, true)) C (B.faces.faceBasis (i, true))
    (B.faces.smooth_faceCoordinates hF.1 _) (B.faces.smooth_faceCoordinates_symm hF.2 _)
    hC hCi (B.faces.face_triangle_subset_source _) (by decide) (B.chartTopVertex_ne i)
    (B.chartTopSegment_subset_source i)
  · rw [B.chartTopSegment_image i]
    have h := B.faces.face_boundary_image (i, true) 0
    change ((B.faces.pair i).upper.boundary 0).map '' Icc (0 : ℝ) 1 = _ at h
    rw [h]
    simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
  · rw [B.faces.face_corner_eq_vertex]
    exact B.vertex_top_eq_chartTopVertex i i.castSucc (Or.inl rfl)

theorem topLeftChord_pos_smul_chart_differential
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i : Fin B.faces.interface.count) :
    ∃ r : ℝ, 0 < r ∧ B.faces.topLeftChord i =
      r • mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
        (B.chartTopVertex i.castSucc - B.chartTopVertex i.succ) := by
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  apply coordinateTriangleVelocity_pos_smul_of_chart_segment
    (B.faces.faceCoordinates (i, true)) C (B.faces.faceBasis (i, true))
    (B.faces.smooth_faceCoordinates hF.1 _) (B.faces.smooth_faceCoordinates_symm hF.2 _)
    hC hCi (B.faces.face_triangle_subset_source _) (by decide) (B.chartTopVertex_ne i).symm
    (by simpa only [segment_symm] using B.chartTopSegment_subset_source i)
  · rw [segment_symm, B.chartTopSegment_image i]
    have h := B.faces.face_boundary_image (i, true) 0
    change ((B.faces.pair i).upper.boundary 0).map '' Icc (0 : ℝ) 1 = _ at h
    rw [h]
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    have he : affineChartSegment (B.faces.faceBasis (i, true) ((0 : Fin 3).succAbove 0))
        (B.faces.faceBasis (i, true) ((0 : Fin 3).succAbove 1)) (1 - t) =
        AffineMap.lineMap (B.faces.faceBasis (i, true) 1)
          (B.faces.faceBasis (i, true) 2) (1 - t) := by
      simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
    dsimp only [Function.comp_apply]
    rw [he]
    change B.faces.faceCoordinates (i, true)
      (AffineMap.lineMap (B.faces.faceBasis (i, true) 1) (B.faces.faceBasis (i, true) 2) (1 - t)) = _
    rw [AffineMap.lineMap_apply_one_sub]
  · rw [B.faces.face_corner_eq_vertex]
    exact B.vertex_top_eq_chartTopVertex i i.succ (Or.inr rfl)

theorem ambientTopFunctional_linear (i : Fin B.faces.interface.count) (v : Plane) :
    (B.ambientTopFunctional i).linear v = (G.frame v).2 -
      (B.faces.interface.piece i).linear 1 * (G.frame v).1 := by
  have he : (B.faces.interface.piece i).linear (G.frame v).1 =
      (G.frame v).1 * (B.faces.interface.piece i).linear 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (B.faces.interface.piece i).linear.map_smul (G.frame v).1 (1 : ℝ)
  change (collarParameterEquiv (collarParameterEquiv.symm (G.frame v))).2 -
    (B.faces.interface.piece i).linear
      (collarParameterEquiv (collarParameterEquiv.symm (G.frame v))).1 = _
  rw [collarParameterEquiv.apply_symm_apply, he, mul_comm]

theorem ambientTopFunctional_cross_left (i j : Fin B.faces.interface.count) :
    (B.ambientTopFunctional j).linear
      (B.chartTopVertex i.castSucc - B.chartTopVertex i.succ) =
      ((B.faces.interface.piece i).linear 1 - (B.faces.interface.piece j).linear 1) *
        (B.faces.interface.cut i.castSucc - B.faces.interface.cut i.succ) := by
  have hz : (B.ambientTopFunctional i).linear
      (B.chartTopVertex i.castSucc - B.chartTopVertex i.succ) = 0 := by
    change (B.ambientTopFunctional i).linear
      (B.chartTopVertex i.castSucc -ᵥ B.chartTopVertex i.succ) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub,
      B.ambientTopFunctional_left_vertex, B.ambientTopFunctional_right_vertex, sub_self]
  rw [B.ambientTopFunctional_linear] at hz ⊢
  simp only [map_sub, Prod.fst_sub, chartTopVertex, G.frame.apply_symm_apply] at hz ⊢
  linarith

theorem ambientTopFunctional_cross_right (i j : Fin B.faces.interface.count) :
    (B.ambientTopFunctional i).linear
      (B.chartTopVertex j.succ - B.chartTopVertex j.castSucc) =
      ((B.faces.interface.piece j).linear 1 - (B.faces.interface.piece i).linear 1) *
        (B.faces.interface.cut j.succ - B.faces.interface.cut j.castSucc) := by
  have h := B.ambientTopFunctional_cross_left j i
  rw [← neg_sub (B.chartTopVertex j.succ) (B.chartTopVertex j.castSucc), map_neg] at h
  linarith

theorem internal_top_positive_sector_rays
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (σ : ℝ) (c : AffineBasis (Fin 3) ℝ Plane)
    (hc1 : c.coord 1 = σ • B.ambientTopFunctional i)
    (hc2 : c.coord 2 = σ • B.ambientTopFunctional j)
    (hslope : 0 < σ * ((B.faces.interface.piece j).linear 1 -
      (B.faces.interface.piece i).linear 1)) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      B.chartTopVertex i.castSucc - B.chartTopVertex i.succ = r • (c 2 - c 0) ∧
      B.chartTopVertex j.succ - B.chartTopVertex i.succ = s • (c 1 - c 0) := by
  let u := B.chartTopVertex i.castSucc - B.chartTopVertex i.succ
  let v := B.chartTopVertex j.succ - B.chartTopVertex i.succ
  have hu1 : (c.coord 1).linear u = 0 := by
    rw [hc1]
    change σ * ((B.ambientTopFunctional i).linear
      (B.chartTopVertex i.castSucc -ᵥ B.chartTopVertex i.succ)) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub,
      B.ambientTopFunctional_left_vertex, B.ambientTopFunctional_right_vertex, sub_self, mul_zero]
  have hv2 : (c.coord 2).linear v = 0 := by
    rw [hc2]
    change σ * ((B.ambientTopFunctional j).linear
      (B.chartTopVertex j.succ -ᵥ B.chartTopVertex i.succ)) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, hij,
      B.ambientTopFunctional_right_vertex, B.ambientTopFunctional_left_vertex, sub_self, mul_zero]
  have hu2 : 0 < (c.coord 2).linear u := by
    rw [hc2]
    change 0 < σ * (B.ambientTopFunctional j).linear u
    rw [B.ambientTopFunctional_cross_left]
    have hcut := B.faces.interface.cut_strictMono (Fin.castSucc_lt_succ (i := i))
    nlinarith [mul_pos hslope (sub_pos.mpr hcut)]
  have hv1 : 0 < (c.coord 1).linear v := by
    rw [hc1]
    change 0 < σ * (B.ambientTopFunctional i).linear v
    dsimp only [v]
    rw [hij, B.ambientTopFunctional_cross_right]
    have hcut := B.faces.interface.cut_strictMono (Fin.castSucc_lt_succ (i := j))
    nlinarith [mul_pos hslope (sub_pos.mpr hcut)]
  refine ⟨(c.coord 2).linear u, (c.coord 1).linear v, hu2, hv1, ?_, ?_⟩
  · simpa only [hu1, zero_smul, zero_add] using affineBasis_direction_expansion c u
  · simpa only [hv2, zero_smul, add_zero] using affineBasis_direction_expansion c v

theorem internal_top_chord_angles_eq_sector_angles
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (σ : ℝ) (c : AffineBasis (Fin 3) ℝ Plane)
    (hc1 : c.coord 1 = σ • B.ambientTopFunctional i)
    (hc2 : c.coord 2 = σ • B.ambientTopFunctional j)
    (hslope : 0 < σ * ((B.faces.interface.piece j).linear 1 -
      (B.faces.interface.piece i).linear 1)) :
    let x := B.faces.vertex (i.succ, true)
    let L := mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
    g.cornerAngle x (B.faces.topOutwardRay i) (B.faces.topLeftChord i) =
      g.cornerAngle x (B.faces.topOutwardRay i) (L (c 2 - c 0)) ∧
    g.cornerAngle x (B.faces.topOutwardRay i) (B.faces.topRightChord j) =
      g.cornerAngle x (B.faces.topOutwardRay i) (L (c 1 - c 0)) := by
  obtain ⟨r, s, hr, hs, hu, hv⟩ := B.internal_top_positive_sector_rays i j hij σ c hc1 hc2 hslope
  obtain ⟨r', hr', hleft⟩ := B.topLeftChord_pos_smul_chart_differential hC hCi i
  obtain ⟨s', hs', hright⟩ := B.topRightChord_pos_smul_chart_differential hC hCi j
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
  have hl : (B.faces.topLeftChord i : Plane) =
      r' • L (B.chartTopVertex i.castSucc - B.chartTopVertex i.succ) := hleft
  have hr : (B.faces.topRightChord j : Plane) =
      s' • L (B.chartTopVertex j.succ - B.chartTopVertex i.succ) := by
    have hp : (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex j.castSucc)
        (B.chartTopVertex j.succ - B.chartTopVertex j.castSucc) : Plane) =
        L (B.chartTopVertex j.succ - B.chartTopVertex i.succ) := by
      exact congrArg (fun k => (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex k)
        (B.chartTopVertex j.succ - B.chartTopVertex k) : Plane)) hij.symm
    exact hright.trans (congrArg (fun v : Plane => s' • v) hp)
  rw [hv, map_smul, smul_smul] at hr
  rw [hu, map_smul, smul_smul] at hl
  dsimp only
  constructor
  · rw [hl, g.cornerAngle_smul_pos_right _ _ _ (mul_pos hr' (show 0 < r from by assumption))]
    rfl
  · rw [hr, g.cornerAngle_smul_pos_right _ _ _ (mul_pos hs' hs)]
    rfl

theorem internal_top_reflex_complement_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.faces.interface.piece i).linear 1 < (B.faces.interface.piece j).linear 1)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc1 : c.coord 1 = B.ambientTopFunctional i)
    (hc2 : c.coord 2 = B.ambientTopFunctional j) :
    let x := B.faces.vertex (i.succ, true)
    let L := mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
    g.cornerAngle x (B.faces.topOutwardRay i) (B.faces.topLeftChord i) +
      g.cornerAngle x (B.faces.topOutwardRay i) (B.faces.topRightChord j) =
        g.cornerAngle x (L (c 1 - c 0)) (L (c 2 - c 0)) := by
  have hang := B.internal_top_chord_angles_eq_sector_angles g hC hCi i j hij 1 c
    (by simpa only [one_smul] using hc1) (by simpa only [one_smul] using hc2)
    (by simpa only [one_mul] using sub_pos.mpr hslope)
  dsimp only at hang ⊢
  rw [hang.1, hang.2]
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
  let v := B.ambientOutwardDirection i.succ
  have h1 : 0 < (c.coord 1).linear v := by
    rw [hc1]
    exact B.ambientTopFunctional_outward_pos i i.succ (Or.inr rfl)
  have h2 : 0 < (c.coord 2).linear v := by
    rw [hc2]
    exact B.ambientTopFunctional_outward_pos j i.succ (Or.inl hij)
  have hne : L v ≠ 0 := by
    intro hz
    have h := B.faces.topOutwardRay_ne_zero
      (linearGraphCoordinates_contMDiff C G.frame hC hCi).1
      (linearGraphCoordinates_contMDiff C G.frame hC hCi).2 i
    apply h
    rw [B.topOutwardRay_eq_chart_differential hC hCi i]
    change B.faces.interface.height i.succ • L v = 0
    rw [hz, smul_zero]
  have hsplit := cornerAngle_split_of_positive_sector_coordinates g
    (B.faces.vertex (i.succ, true)) c L v h1 h2 hne
  dsimp only [TangentSpace] at hsplit ⊢
  rw [B.topOutwardRay_eq_chart_differential hC hCi i,
    g.cornerAngle_smul_pos_left _ _ _ (B.faces.interface.vertex_height_bounds i.succ).1,
    g.cornerAngle_smul_pos_left _ _ _ (B.faces.interface.vertex_height_bounds i.succ).1]
  exact (add_comm _ _).trans hsplit.symm

theorem internal_top_convex_complement_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.faces.interface.piece j).linear 1 < (B.faces.interface.piece i).linear 1)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc1 : c.coord 1 = -B.ambientTopFunctional i)
    (hc2 : c.coord 2 = -B.ambientTopFunctional j) :
    let x := B.faces.vertex (i.succ, true)
    let L := mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
    g.cornerAngle x (B.faces.topOutwardRay i) (B.faces.topLeftChord i) +
      g.cornerAngle x (B.faces.topOutwardRay i) (B.faces.topRightChord j) =
        2 * Real.pi - g.cornerAngle x (L (c 1 - c 0)) (L (c 2 - c 0)) := by
  have hang := B.internal_top_chord_angles_eq_sector_angles g hC hCi i j hij (-1) c
    (by simpa only [neg_one_smul] using hc1) (by simpa only [neg_one_smul] using hc2)
    (by linarith)
  dsimp only at hang ⊢
  rw [hang.1, hang.2]
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
  let v := B.ambientOutwardDirection i.succ
  have h1 : 0 < (c.coord 1).linear (-v) := by
    rw [hc1]
    change 0 < -(B.ambientTopFunctional i).linear (-v)
    rw [map_neg, neg_neg]
    exact B.ambientTopFunctional_outward_pos i i.succ (Or.inr rfl)
  have h2 : 0 < (c.coord 2).linear (-v) := by
    rw [hc2]
    change 0 < -(B.ambientTopFunctional j).linear (-v)
    rw [map_neg, neg_neg]
    exact B.ambientTopFunctional_outward_pos j i.succ (Or.inl hij)
  have hne : L (-v) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    intro hz
    have h := B.faces.topOutwardRay_ne_zero
      (linearGraphCoordinates_contMDiff C G.frame hC hCi).1
      (linearGraphCoordinates_contMDiff C G.frame hC hCi).2 i
    apply h
    rw [B.topOutwardRay_eq_chart_differential hC hCi i]
    change B.faces.interface.height i.succ • L v = 0
    rw [hz, smul_zero]
  have hsplit := cornerAngle_split_of_positive_sector_coordinates g
    (B.faces.vertex (i.succ, true)) c L (-v) h1 h2 hne
  dsimp only [TangentSpace] at hsplit ⊢
  rw [L.map_neg v, g.cornerAngle_neg_left, g.cornerAngle_neg_left] at hsplit
  rw [B.topOutwardRay_eq_chart_differential hC hCi i,
    g.cornerAngle_smul_pos_left _ _ _ (B.faces.interface.vertex_height_bounds i.succ).1,
    g.cornerAngle_smul_pos_left _ _ _ (B.faces.interface.vertex_height_bounds i.succ).1]
  change g.cornerAngle _ (L v) (L (c 2 - c 0)) +
    g.cornerAngle _ (L v) (L (c 1 - c 0)) =
      2 * Real.pi - g.cornerAngle _ (L (c 1 - c 0)) (L (c 2 - c 0))
  linarith

theorem internal_top_refined_vertex_fan_eq_convex_sector
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.faces.interface.piece j).linear 1 < (B.faces.interface.piece i).linear 1)
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = B.chartTopVertex i.succ)
    (hc1 : c.coord 1 = -B.ambientTopFunctional i)
    (hc2 : c.coord 2 = -B.ambientTopFunctional j) :
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (C (c 0))) =
      g.cornerAngle (C (c 0))
        (mfderiv (𝓡 2) (𝓡 2) C (c 0) (c 1 - c 0))
        (mfderiv (𝓡 2) (𝓡 2) C (c 0) (c 2 - c 0)) := by
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  have hfan := B.faces.internal_top_refined_vertex_fan g hF.1 hF.2 lines i j hij
  have hang := B.internal_top_convex_complement_angle g hC hCi i j hij hslope c hc1 hc2
  dsimp only at hang
  have hv := B.vertex_top_eq_chartTopVertex i i.succ (Or.inr rfl)
  rw [← hc0] at hv
  let angle : S → Plane → Plane → ℝ := fun x v w => g.cornerAngle x v w
  have hres : (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (B.faces.vertex (i.succ, true))) = angle (B.faces.vertex (i.succ, true))
          (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ) (c 1 - c 0))
          (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ) (c 2 - c 0)) := by
    dsimp only [angle]
    linarith
  have hd (k : Fin 3) : (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
      (c k - c 0) : Plane) = mfderiv (𝓡 2) (𝓡 2) C (c 0) (c k - c 0) :=
    congrArg (fun z : Plane => (mfderiv (𝓡 2) (𝓡 2) C z (c k - c 0) : Plane)) hc0.symm
  rw [hv, hd 1, hd 2] at hres
  exact hres

theorem internal_top_refined_vertex_fan_eq_reflex_sector
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.faces.interface.piece i).linear 1 < (B.faces.interface.piece j).linear 1)
    (c : AffineBasis (Fin 3) ℝ Plane) (hc0 : c 0 = B.chartTopVertex i.succ)
    (hc1 : c.coord 1 = B.ambientTopFunctional i)
    (hc2 : c.coord 2 = B.ambientTopFunctional j) :
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (C (c 0))) =
      2 * Real.pi - g.cornerAngle (C (c 0))
        (mfderiv (𝓡 2) (𝓡 2) C (c 0) (c 1 - c 0))
        (mfderiv (𝓡 2) (𝓡 2) C (c 0) (c 2 - c 0)) := by
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  have hfan := B.faces.internal_top_refined_vertex_fan g hF.1 hF.2 lines i j hij
  have hang := B.internal_top_reflex_complement_angle g hC hCi i j hij hslope c hc1 hc2
  dsimp only at hang
  have hv := B.vertex_top_eq_chartTopVertex i i.succ (Or.inr rfl)
  rw [← hc0] at hv
  let angle : S → Plane → Plane → ℝ := fun x v w => g.cornerAngle x v w
  have hres : (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (B.faces.vertex (i.succ, true))) = 2 * Real.pi - angle (B.faces.vertex (i.succ, true))
          (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ) (c 1 - c 0))
          (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ) (c 2 - c 0)) := by
    dsimp only [angle]
    linarith
  have hd (k : Fin 3) : (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
      (c k - c 0) : Plane) = mfderiv (𝓡 2) (𝓡 2) C (c 0) (c k - c 0) :=
    congrArg (fun z : Plane => (mfderiv (𝓡 2) (𝓡 2) C z (c k - c 0) : Plane)) hc0.symm
  rw [hv, hd 1, hd 2] at hres
  exact hres

theorem chartTopChord_direction (i : Fin B.faces.interface.count) :
    B.chartTopVertex i.succ - B.chartTopVertex i.castSucc =
      (B.faces.interface.cut i.succ - B.faces.interface.cut i.castSucc) •
        G.frame.symm (1, (B.faces.interface.piece i).linear 1) := by
  have hz : (B.ambientTopFunctional i).linear
      (B.chartTopVertex i.succ - B.chartTopVertex i.castSucc) = 0 := by
    change (B.ambientTopFunctional i).linear
      (B.chartTopVertex i.succ -ᵥ B.chartTopVertex i.castSucc) = 0
    rw [AffineMap.linearMap_vsub, vsub_eq_sub,
      B.ambientTopFunctional_right_vertex, B.ambientTopFunctional_left_vertex, sub_self]
  rw [B.ambientTopFunctional_linear] at hz
  simp only [map_sub, chartTopVertex, G.frame.apply_symm_apply, Prod.fst_sub, Prod.snd_sub] at hz
  apply G.frame.injective
  simp only [map_sub, map_smul, chartTopVertex, G.frame.apply_symm_apply]
  apply Prod.ext
  · simp
  · change _ = (B.faces.interface.cut i.succ - B.faces.interface.cut i.castSucc) *
      (B.faces.interface.piece i).linear 1
    simp only [Prod.snd_sub]
    linarith

theorem internal_top_straight_complement_angle
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.faces.interface.piece i).linear 1 = (B.faces.interface.piece j).linear 1) :
    g.cornerAngle (B.faces.vertex (i.succ, true))
        (B.faces.topOutwardRay i) (B.faces.topLeftChord i) +
      g.cornerAngle (B.faces.vertex (i.succ, true))
        (B.faces.topOutwardRay i) (B.faces.topRightChord j) = Real.pi := by
  obtain ⟨r, hr, hleft⟩ := B.topLeftChord_pos_smul_chart_differential hC hCi i
  obtain ⟨s, hs, hright⟩ := B.topRightChord_pos_smul_chart_differential hC hCi j
  let L : Plane →L[ℝ] Plane := mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex i.succ)
  let u := G.frame.symm (1, (B.faces.interface.piece i).linear 1)
  let di := B.faces.interface.cut i.succ - B.faces.interface.cut i.castSucc
  let dj := B.faces.interface.cut j.succ - B.faces.interface.cut j.castSucc
  have hdi : 0 < di := sub_pos.mpr (B.faces.interface.cut_strictMono (Fin.castSucc_lt_succ (i := i)))
  have hdj : 0 < dj := sub_pos.mpr (B.faces.interface.cut_strictMono (Fin.castSucc_lt_succ (i := j)))
  have hld : B.chartTopVertex i.castSucc - B.chartTopVertex i.succ = -(di • u) := by
    rw [← B.chartTopChord_direction i]
    exact (neg_sub _ _).symm
  have hrd : B.chartTopVertex j.succ - B.chartTopVertex i.succ = dj • u := by
    rw [hij, B.chartTopChord_direction j]
    simp only [u, hslope, dj]
  have hl : (B.faces.topLeftChord i : Plane) = (r * di) • (-L u) := by
    change (B.faces.topLeftChord i : Plane) = r • L _ at hleft
    rw [hld, map_neg, map_smul, smul_neg, ← neg_smul, smul_smul] at hleft
    simpa only [neg_mul, neg_smul, smul_neg] using hleft
  have hp : (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex j.castSucc)
      (B.chartTopVertex j.succ - B.chartTopVertex j.castSucc) : Plane) =
      L (B.chartTopVertex j.succ - B.chartTopVertex i.succ) :=
    congrArg (fun k => (mfderiv (𝓡 2) (𝓡 2) C (B.chartTopVertex k)
      (B.chartTopVertex j.succ - B.chartTopVertex k) : Plane)) hij.symm
  have hray : (B.faces.topRightChord j : Plane) = (s * dj) • L u := by
    have he := hright.trans (congrArg (fun v : Plane => s • v) hp)
    rw [hrd, map_smul, smul_smul] at he
    exact he
  rw [hl, hray, g.cornerAngle_smul_pos_right _ _ _ (mul_pos hr hdi),
    g.cornerAngle_smul_pos_right _ _ _ (mul_pos hs hdj), g.cornerAngle_neg_right]
  ring

theorem internal_top_refined_vertex_fan_eq_pi_of_slope_eq
    (g : RiemannianMetric 2 S)
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (lines : (Fin B.faces.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (i j : Fin B.faces.interface.count) (hij : i.succ = j.castSucc)
    (hslope : (B.faces.interface.piece i).linear 1 = (B.faces.interface.piece j).linear 1) :
    (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (C (B.chartTopVertex i.succ))) = Real.pi := by
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCi
  have hfan := B.faces.internal_top_refined_vertex_fan g hF.1 hF.2 lines i j hij
  have hang := B.internal_top_straight_complement_angle g hC hCi i j hij hslope
  have hres : (∑ p : Fin B.faces.interface.count × Bool,
      meshVertexAngleContribution g (B.faces.faceCoordinates p)
        ((TriangleMesh.single (B.faces.faceBasis p) (B.faces.faceBasis p).ind).refineByLines (lines p))
        (B.faces.vertex (i.succ, true))) = Real.pi := by linarith
  rwa [B.vertex_top_eq_chartTopVertex i i.succ (Or.inr rfl)] at hres

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

end PoincareConjecture.Topology.Surface
