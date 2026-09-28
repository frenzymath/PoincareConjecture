import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaBarrier
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaInputs
import Mathlib.Analysis.Calculus.Deriv.Slope











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M65Filling

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

set_option maxHeartbeats 1200000 in






theorem embedded_filling_area_inequality_of_attainment_gaussBonnet
    [T2Space M] [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (attainment : ∀ q ∈ Ioo a b, ∀ gamma : C1FreeLoopSpace (M := M),
      ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma) →
      (∀ x, curveVelocity (n := 3) (periodicFreeLoop gamma) x ≠ 0) →
      Function.Injective (gamma : LoopCircle → M) →
      Nonempty (LipschitzSpanningDisk (F.metric q) gamma) →
      Nonempty (M65MinimalDisk (F.metric q) (F.connection q) gamma))
    (gaussBonnet : ∀ q ∈ Ioo a b,
      M65SuppliedDiskGaussBonnet (F.metric q) (F.connection q)) :
    M65EmbeddedFillingAreaInequality F := by
  intro J hJ hJF C q hq hinj epsilon _hepsilon hresidual delta hdelta
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop (C.loops q)) :=
    C.joint_smooth.comp_contMDiff
      (contDiff_id.prodMk (contDiff_const (c := q))).contMDiff
      (fun _ => ⟨mem_univ _, hq⟩)
  obtain ⟨S⟩ := attainment q (hJF hq) (C.loops q) hsmooth (C.immersed q hq) hinj (C.filled q hq)
  obtain ⟨E, W, hW, hagree, hRI, hE0, hbarrier, hder⟩ :=
    exists_differentiable_barrier F hJ hJF C hq hinj S
  obtain ⟨H, hH⟩ := exists_curvature_section (F.connection q) (C.loops q) hinj
  obtain ⟨hQI, hHI, hGB⟩ := gaussBonnet q (hJF hq) (C.loops q) S
    hsmooth (C.immersed q hq) hinj H hH
  have hWI := radial_flux_integrable (F.metric q) S.boundary_regular W hW.continuous
  have hres (x : ℝ) : (F.metric q).tangentNorm (periodicFreeLoop (C.loops q) x)
      (W (periodicFreeLoop (C.loops q) x) - H (periodicFreeLoop (C.loops q) x)) ≤ epsilon := by
    rw [hagree x, hH x]
    exact hresidual x
  have hflux := radial_flux_le_of_residual S hsmooth (C.immersed q hq) W H hres hWI hHI
  obtain ⟨hscalarI, hscalar⟩ := scalar_area_lower_bound F (Ioo_subset_Icc_self (hJF hq)) S
  let R := ∫ z in loopDiskSet, m65PlaneRicciTraceDensity (F.connection q) S.disk.map z
  let B := ∫ theta in (-Real.pi)..Real.pi,
    (F.metric q).inner (S.disk.map (Proofs.M58.angularPoint theta))
      (W (S.disk.map (Proofs.M58.angularPoint theta)))
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
        (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))
  let bound := -2 * Real.pi - flowScalarCurvatureInfimum F q *
    fillingArea (F.metric q) (C.loops q) / 2 +
    epsilon * freeLoopLength (F.metric q) (C.loops q)
  have hQeq : (∫ z in loopDiskSet,
      m65PlaneRicciTraceDensity (F.connection q) S.disk.map z -
        (F.connection q).scalarCurvature (S.disk.map z) *
          m60AreaDensity (F.metric q) S.disk.map z / 2) =
      R - ∫ z in loopDiskSet, (F.connection q).scalarCurvature (S.disk.map z) *
        m60AreaDensity (F.metric q) S.disk.map z / 2 :=
    integral_sub hRI hscalarI
  rw [hQeq] at hGB
  have hbound : -R + B ≤ bound := by
    dsimp only [bound, R, B]
    linarith [hGB, hflux, hscalar]
  have hslope : Tendsto (fun h : ℝ => (E (q + h) - E q) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (-R + B)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hder.tendsto_slope_zero_right
  have hslope' : ∀ᶠ h in 𝓝[>] (0 : ℝ), (E (q + h) - E q) / h < -R + B + delta :=
    hslope.eventually (Iio_mem_nhds (by linarith))
  have hshift : Tendsto (fun h : ℝ => q + h) (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds.add tendsto_id :
        Tendsto (fun h : ℝ => q + h) (𝓝 (0 : ℝ)) (𝓝 (q + 0))).mono_left nhdsWithin_le_nhds)
  filter_upwards [hslope', hshift.eventually hbarrier, self_mem_nhdsWithin] with h hs hb hh
  have hpos : 0 < h := hh
  have hnum : fillingArea (F.metric (q + h)) (C.loops (q + h)) -
      fillingArea (F.metric q) (C.loops q) ≤ E (q + h) - E q := by
    rw [hE0]
    exact sub_le_sub_right hb _
  exact (div_le_div_of_nonneg_right hnum hpos.le).trans
    (hs.le.trans (by change -R + B + delta ≤ bound + delta; linarith))

end PoincareConjecture.M65Filling
