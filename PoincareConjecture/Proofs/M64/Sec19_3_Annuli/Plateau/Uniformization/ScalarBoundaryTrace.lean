import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryCharts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.SobolevLocalization
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Embedding.Continuous














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
private abbrev halfSpace : Set Plane := {x | 0 < x 0}

private theorem mem_closure_halfSpace {x : Plane} (hx : x 0 = 0) : x ∈ closure halfSpace := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let y : Plane := x + (ε / 2) • EuclideanSpace.single (0 : Fin 2) 1
  refine ⟨y, ?_, ?_⟩
  · change 0 < (x + (ε / 2) • EuclideanSpace.single (0 : Fin 2) 1 : Plane) 0
    simpa [hx] using half_pos hε
  · change dist x (x + (ε / 2) • EuclideanSpace.single (0 : Fin 2) 1) < ε
    rw [dist_self_add_right, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith







theorem smooth_representative_zero_on_halfSpace_boundary
    {u v : Plane → ℝ} (huc : HasCompactSupport u)
    (hu0 : Weak.MemW01p 2 u halfSpace) (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (huv : u =ᵐ[volume.restrict halfSpace] v)
    {x : Plane} (hx : x 0 = 0) : v x = 0 := by
  have hH : IsOpen halfSpace := BoundaryTangential.isOpen_halfSpace
  have hv3 : Euclidean.MemWkp 3 2 v halfSpace :=
    (Euclidean.MemWkp_of_smooth_compactSupport isOpen_univ hv hvc (subset_univ _)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) 3).mono_set (by norm_num) hH (subset_univ _)
  have hu3 : Euclidean.MemWkp 3 2 u halfSpace :=
    (Euclidean.MemWkp_congr_ae (by norm_num) hH huv).mpr hv3
  obtain ⟨F, hF, hFu, hzero⟩ := BoundaryEmbedding.exists_continuous_zero_extension huc hu0 hu3
  have heq : EqOn v F halfSpace := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hH hv.continuous.continuousOn hF.continuousOn
    filter_upwards [huv, ae_restrict_of_ae hFu, ae_restrict_mem hH.measurableSet]
      with y hyv hyF hy
    rw [indicator_of_mem (show y ∈ halfSpace from hy)] at hyF
    exact hyv.symm.trans hyF
  have hxEq := heq.closure hv.continuous hF (mem_closure_halfSpace hx)
  exact hxEq.trans (hzero x hx.le)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)








theorem H1Zero_smooth_annular_trace_zero (w : H1Zero D scalarAnnulus)
    {V : Plane → ℝ} (hV : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ V)
    (hwV : (toL2 D scalarAnnulus w : Plane → ℝ) =ᵐ[g.volumeMeasure.restrict scalarAnnulus] V)
    {a : Plane} (ha : ‖a‖ = 1 ∨ ‖a‖ = 2) : V a = 0 := by
  obtain ⟨e, hae, he, hei, hzero, hflat⟩ := exists_scalarAnnulus_boundary_chart ha
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 2) a).mem_iff.mp
    (e.open_target.mem_nhds hae)
  let U := chartPullback e (fun y => b y * toL2 D scalarAnnulus w y)
  let Q := chartPullback e (fun y => b y * V y)
  have hUc : HasCompactSupport U := hasCompactSupport_chartPullback e
    b.hasCompactSupport.mul_right (tsupport_mul_subset_left.trans hb)
  have hQc : HasCompactSupport Q := hasCompactSupport_chartPullback e
    b.hasCompactSupport.mul_right (tsupport_mul_subset_left.trans hb)
  have hQs : ContDiff ℝ ∞ Q := contDiff_chartPullback e he (b.contMDiff.mul hV)
    b.hasCompactSupport.mul_right (tsupport_mul_subset_left.trans hb)
  have hU0 : Weak.MemW01p 2 U halfSpace :=
    Boundary.memW01p_chartPullback_toL2 e he hei b b.contMDiff b.hasCompactSupport hb hflat w
  let K := e.symm '' tsupport (b : Plane → ℝ)
  have hK : IsCompact K := b.hasCompactSupport.isCompact.image_of_continuousOn
    (e.symm.continuousOn.mono hb)
  have hKs : K ⊆ e.source := by
    rintro z ⟨y, hy, rfl⟩
    exact e.map_target (hb hy)
  have hglobal : scalarAnnulus.indicator (toL2 D scalarAnnulus w : Plane → ℝ)
      =ᵐ[g.volumeMeasure] scalarAnnulus.indicator V := by
    filter_upwards [(ae_restrict_iff' scalarAnnulus_isOpen.measurableSet).mp hwV] with y hy
    by_cases hya : y ∈ scalarAnnulus
    · simp only [indicator_of_mem hya, hy hya]
    · simp only [indicator_of_notMem hya]
  have hcomp := (ae_restrict_iff' hK.measurableSet).mp
    (g.ae_comp_on_compact e he hei hK hKs hglobal)
  have hUQ : U =ᵐ[volume.restrict halfSpace] Q := by
    filter_upwards [ae_restrict_of_ae hcomp,
      ae_restrict_mem
        (show IsOpen halfSpace from BoundaryTangential.isOpen_halfSpace).measurableSet]
      with z hz hzH
    by_cases hzs : z ∈ e.source
    · simp only [U, Q, chartPullback_apply e _ hzs]
      by_cases hzb : b (e z) = 0
      · simp only [hzb, zero_mul]
      · have hzK : z ∈ K :=
          ⟨e z, subset_tsupport (b : Plane → ℝ) hzb, e.left_inv hzs⟩
        have hza := (hflat z hzs).mpr hzH
        have h := hz hzK
        simp only [indicator_of_mem hza] at h
        rw [h]
    · simp only [U, Q, chartPullback, indicator_of_notMem hzs]
  have hQzero := smooth_representative_zero_on_halfSpace_boundary hUc hU0 hQs hQc hUQ hzero
  change chartPullback e (fun y => b y * V y) (e.symm a) = 0 at hQzero
  rw [chartPullback_apply e _ (e.map_target hae), e.right_inv hae, b.eq_one, one_mul] at hQzero
  exact hQzero

end PoincareConjecture.M64Uniformization
