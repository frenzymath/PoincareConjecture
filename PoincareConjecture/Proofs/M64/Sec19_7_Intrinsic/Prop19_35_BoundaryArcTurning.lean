import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcParameter
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryArcTurningDifferential
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem abs_integral_le_of_open_arc_parameter
    {f density phi : ℝ → ℝ} {lo hi : ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hdensity : Continuous density)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt phi (deriv phi t) (Ioo (0 : ℝ) 1) t)
    (hinj : InjOn phi (Ioo (0 : ℝ) 1))
    (himage : phi '' Ioo (0 : ℝ) 1 = Ioo lo hi) (hle : lo ≤ hi)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1,
      |f t| ≤ |deriv phi t| * density (phi t)) :
    |∫ t in (0 : ℝ)..1, f t| ≤ ∫ s in lo..hi, density s := by
  have himageInt : IntegrableOn density (phi '' Ioo (0 : ℝ) 1) := by
    rw [himage]
    exact hdensity.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hjacInt : IntegrableOn (fun t => |deriv phi t| * density (phi t))
      (Ioo (0 : ℝ) 1) := by
    simpa only [smul_eq_mul] using
      (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
        hderiv hinj density).mp himageInt
  have habsInt : IntegrableOn (fun t => |f t|) (Ioo (0 : ℝ) 1) :=
    (hf.abs.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  calc
    _ = |∫ t in Ioo (0 : ℝ) 1, f t| := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    _ ≤ ∫ t in Ioo (0 : ℝ) 1, |f t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioo (0 : ℝ) 1, |deriv phi t| * density (phi t) :=
      setIntegral_mono_on habsInt hjacInt measurableSet_Ioo hbound
    _ = ∫ s in Ioo lo hi, density s := by
      simpa only [himage, smul_eq_mul] using
        (integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj density).symm
    _ = ∫ s in lo..hi, density s := by
      rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]

theorem m64Intrinsic_coordinate_side_boundary_arc_turning_bound
    (N : IntrinsicAnnulus)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame N.metric (coordinateTriangleChart F b))
    {i j : Fin 3} (hij : i ≠ j) {radius : ℝ} (hradius : radius ≠ 0)
    {a0 a1 : ℝ} (hinj : InjOn (intrinsicAnnulusBoundary radius) (Icc a0 a1))
    (himage : (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) '' Icc (0 : ℝ) 1 ⊆
      intrinsicAnnulusBoundary radius '' Icc a0 a1) :
    ∃ lo hi : ℝ, a0 ≤ lo ∧ lo < hi ∧ hi ≤ a1 ∧
      (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) '' Icc (0 : ℝ) 1 =
        intrinsicAnnulusBoundary radius '' Icc lo hi ∧
      |coordinateTriangleTurningIntegral N.connection F b Q i j| ≤
        intrinsicGeodesicCurvatureIntegral N.metric N.connection radius lo hi := by
  let eta : ℝ → AnnulusCoordinates := fun t => F (AffineMap.lineMap (b i) (b j) t)
  let V := coordinateTriangleSideField F b i j
  let W := coordinateTriangleSideUnitField N.metric F b i j
  have hsrc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap (b i) (b j) t ∈ F.source :=
    hsource ((convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self i))
      (subset_convexHull ℝ _ (mem_range_self j)) ht)
  have htarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : eta t ∈ F.target :=
    F.map_source (hsrc t ht)
  have hchart (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      eta t ∈ (coordinateTriangleChart F b).source := by
    rw [coordinateTriangleChart_source]
    exact htarget t ht
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
    exact LeviCivitaData.chartField_ne_zero (coordinateTriangleChart F b)
      (coordinateTriangleChart_smooth F b hFi)
      (coordinateTriangleChart_smooth_symm F b hF) hv (hchart t ht)
  have hgammaReg (s : ℝ) (_hs : s ∈ Icc a0 a1) :
      deriv (intrinsicAnnulusBoundary radius) s ≠ 0 := by
    intro hz
    have hpos := m64Intrinsic_boundarySpeed_pos N hradius s
    rw [intrinsicBoundarySpeed, m64Intrinsic_curveVelocity_eq_deriv, hz] at hpos
    simp only [RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero, lt_self_iff_false] at hpos
  obtain ⟨phi, _, hmap, heq, hphiinj, _, hsmooth, hclosed, hopen⟩ :=
    m64Intrinsic_exists_arc_parameter (m64Intrinsic_contDiff_boundary radius) hinj hgammaReg
      (fun t ht => (hside t ht).1) hinjeta hreg himage
  let lo := min (phi 0) (phi 1)
  let hi := max (phi 0) (phi 1)
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hlo : a0 ≤ lo := le_min (hmap hzero).1 (hmap hone).1
  have hhi : hi ≤ a1 := max_le (hmap hzero).2 (hmap hone).2
  have hlohi : lo < hi := min_lt_max.mpr (fun h => zero_ne_one (hphiinj hzero hone h))
  have hexact : eta '' Icc (0 : ℝ) 1 = intrinsicAnnulusBoundary radius '' Icc lo hi := by
    calc
      _ = (intrinsicAnnulusBoundary radius ∘ phi) '' Icc (0 : ℝ) 1 := by
        apply image_congr
        intro t ht
        exact heq ht
      _ = intrinsicAnnulusBoundary radius '' (phi '' Icc (0 : ℝ) 1) := image_comp _ _ _
      _ = _ := by rw [hclosed]
  refine ⟨lo, hi, hlo, hlohi, hhi, hexact, ?_⟩
  let turn : ℝ → ℝ := fun t => N.connection.surfaceTurningForm Q.first Q.second W V (eta t)
  let density : ℝ → ℝ := fun s => intrinsicGeodesicCurvature N.metric N.connection radius s *
    intrinsicBoundarySpeed N.metric radius s
  have hQ1 : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% Q.first) F.target := by
    simpa only [coordinateTriangleChart_source] using Q.smooth_first
  have hQ2 : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% Q.second) F.target := by
    simpa only [coordinateTriangleChart_source] using Q.smooth_second
  have hWsmooth : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% W) F.target :=
    coordinateTriangleSideUnitField_smooth N.metric F b hF hFi hij
  have hVsmooth : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% V) F.target := by
    intro x hx
    exact (LeviCivitaData.contMDiffAt_chartField (coordinateTriangleChart F b)
      (coordinateTriangleChart_smooth F b hFi)
      (coordinateTriangleChart_smooth_symm F b hF)
      (by rwa [coordinateTriangleChart_source])
      (standardTriangleVertex j - standardTriangleVertex i)).contMDiffWithinAt
  have hturn : ContinuousOn turn (Icc (0 : ℝ) 1) :=
    N.connection.continuousOn_surfaceTurningForm_comp_curve F.open_target
      hQ1 hQ2 hWsmooth hVsmooth
      (fun t ht => (hside t ht).1.continuousAt.continuousWithinAt)
      (fun t ht => htarget t ht)
  change |∫ t in (0 : ℝ)..1, turn t| ≤ ∫ s in lo..hi, density s
  apply abs_integral_le_of_open_arc_parameter hturn
    (m64Intrinsic_continuous_turning_density N hradius)
    (fun t ht => ((hsmooth t ht).1.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt)
    (hphiinj.mono Ioo_subset_Icc_self) hopen hlohi.le
  intro t ht
  have ht' := Ioo_subset_Icc_self ht
  have heta : eta =ᶠ[𝓝 t] intrinsicAnnulusBoundary radius ∘ phi := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact heq (Ioo_subset_Icc_self hs)
  have hvelocity : ∀ᶠ s in 𝓝 t, V (eta s) = deriv eta s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (hside s (Ioo_subset_Icc_self hs)).2.symm
  have hW : DifferentiableAt ℝ W (eta t) := by
    have h := hWsmooth.contMDiffAt (F.open_target.mem_nhds (htarget t ht'))
    have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
    have hW' : ContMDiffAt (𝓡 2) (𝓡 2) ∞ W (eta t) := by
      simpa only [trivializationAt_model_space_apply] using hh
    exact (contMDiffAt_iff_contDiffAt.mp hW').differentiableAt (by simp)
  exact m64Intrinsic_normalized_boundary_turning_bound N hradius Q.first Q.second
    ((hsmooth t ht).1.of_le (by norm_cast)) (hsmooth t ht).2 heta hvelocity hW
    (Q.unit_first _ (hchart t ht')) (Q.unit_second _ (hchart t ht'))
    (Q.orthogonal _ (hchart t ht'))

end PoincareConjecture
