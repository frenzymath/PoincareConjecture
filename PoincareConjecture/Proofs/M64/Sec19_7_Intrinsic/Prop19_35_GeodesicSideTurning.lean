import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicTurning
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopReparametrization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_coordinate_side_geodesic_turning_eq_zero
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    {i j : Fin 3} (hij : i ≠ j)
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ}
    (hgeo : g.IsGeodesicOn gamma (Icc 0 T))
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hunit : ∀ p ∈ Icc 0 T, g.inner (gamma p) (deriv gamma p) (deriv gamma p) = 1)
    (himage : (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) '' Icc (0 : ℝ) 1 ⊆
      gamma '' Icc 0 T) :
    coordinateTriangleTurningIntegral D F b Q i j = 0 := by
  let eta : ℝ → AnnulusCoordinates := fun t => F (AffineMap.lineMap (b i) (b j) t)
  let V := coordinateTriangleSideField F b i j
  let W := coordinateTriangleSideUnitField g F b i j
  have hsrc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap (b i) (b j) t ∈ F.source :=
    hsource ((convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self i)) (subset_convexHull ℝ _ (mem_range_self j)) ht)
  have htarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : eta t ∈ F.target := F.map_source (hsrc t ht)
  have hinjeta : InjOn eta (Icc (0 : ℝ) 1) := by
    intro s hs t ht heq
    exact AffineMap.lineMap_injective ℝ (b.ind.injective.ne hij)
      (F.injOn (hsrc s hs) (hsrc t ht) heq)
  have hside (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ eta t ∧ deriv eta t = V (eta t) := by
    have h := coordinateTriangle_side_velocity F b hF hFi hsource i j ht
    refine ⟨contMDiffAt_iff_contDiffAt.mp h.1, ?_⟩
    have hd := h.2
    rw [mfderiv_eq_fderiv] at hd
    change fderiv ℝ eta t 1 = V (eta t) at hd
    simpa only [fderiv_eq_smul_deriv, one_smul] using hd
  have hv : standardTriangleVertex j - standardTriangleVertex i ≠ 0 := by
    intro hz
    have h := congrArg (triangleParameterEquiv b) (sub_eq_zero.mp hz)
    rw [triangleParameterEquiv_vertex, triangleParameterEquiv_vertex] at h
    exact hij (b.ind.injective h).symm
  have hreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : deriv eta t ≠ 0 := by
    rw [(hside t ht).2]
    apply LeviCivitaData.chartField_ne_zero (coordinateTriangleChart F b)
      (coordinateTriangleChart_smooth F b hFi)
      (coordinateTriangleChart_smooth_symm F b hF) hv
    rw [coordinateTriangleChart_source]
    exact htarget t ht
  have hzero (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (hne : eta t ≠ gamma 0) :
      D.surfaceTurningForm Q.first Q.second W V (eta t) = 0 := by
    obtain ⟨p, hp, hpt⟩ := himage ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    have hp0 : 0 < p := lt_of_le_of_ne hp.1 (by
      intro h
      exact hne (hpt.symm.trans (congrArg gamma h.symm)))
    have hpT : p < T := lt_of_le_of_ne hp.2 (by
      intro h
      exact hne (hpt.symm.trans ((congrArg gamma h).trans hend.symm)))
    have hgammaReg : deriv gamma p ≠ 0 := by
      intro hz
      have hu := hunit p hp
      simp only [hz, map_zero] at hu
      norm_num at hu
    obtain ⟨phi, hphi, hphip, hpd, heq⟩ :=
      m64Intrinsic_exists_local_loop_reparametrization hg hend hinj ⟨hp0, hpT⟩ hgammaReg
        (hside t (Ioo_subset_Icc_self ht)).1 hpt.symm
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
          (fun s hs => himage ⟨s, Ioo_subset_Icc_self hs, rfl⟩))
        (hreg t (Ioo_subset_Icc_self ht))
    have hT : DifferentiableAt ℝ W (eta t) := by
      have h := (coordinateTriangleSideUnitField_smooth g F b hF hFi hij).contMDiffAt
        (F.open_target.mem_nhds (htarget t (Ioo_subset_Icc_self ht)))
      have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
      have hW' : ContMDiffAt (𝓡 2) (𝓡 2) ∞ W (eta t) := by
        simpa only [trivializationAt_model_space_apply] using hh
      exact (contMDiffAt_iff_contDiffAt.mp hW').differentiableAt (by simp)
    apply m64Intrinsic_normalized_geodesic_turning_eq_zero D Q.first Q.second hg hgeo
      (hphip.symm ▸ hp) (hphi.of_le (by norm_cast)) hpd heq _ _ hT
    · rw [hphip]
      filter_upwards [isOpen_Ioo.mem_nhds (show p ∈ Ioo (0 : ℝ) T from ⟨hp0, hpT⟩)] with s hs
      exact hunit s (Ioo_subset_Icc_self hs)
    · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (hside s (Ioo_subset_Icc_self hs)).2.symm
  have hfinite : {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ eta t = gamma 0}.Finite := by
    apply Set.Subsingleton.finite
    intro s hs t ht
    exact hinjeta hs.1 ht.1 (hs.2.trans ht.2.symm)
  unfold coordinateTriangleTurningIntegral
  apply intervalIntegral.integral_zero_ae
  filter_upwards [hfinite.countable.ae_notMem volume, volume.ae_ne (1 : ℝ)] with t hnot h1 ht
  have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
  exact hzero t ⟨ht'.1, lt_of_le_of_ne ht'.2 h1⟩
    (fun heq => hnot ⟨⟨ht'.1.le, ht'.2⟩, heq⟩)

end PoincareConjecture
