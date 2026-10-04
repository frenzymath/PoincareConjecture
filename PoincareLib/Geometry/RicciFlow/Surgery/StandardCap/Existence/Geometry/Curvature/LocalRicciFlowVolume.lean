import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Basic.LocalCalibratedImageVolume
import PoincareLib.Geometry.RicciFlow.MetricComparison

/-!
# Volume preservation on a region with bounded Ricci curvature

The pointwise time comparison and the local calibrated-volume theorem
apply to the identity on the actual open region. Distances between
arbitrary exterior points are not compared globally.
Source: Morgan-Tian Theorem 12.29, pp. 324-325;
exterior-scalar-and-second-blowup.md, sections 5-6.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.M34

/-- Local Ricci control preserves the calibrated volume of every
measurable subset of the controlled open region, in arbitrary dimension.
No completeness or finite-volume premise is required (Theorem 12.29). -/
theorem calibratedMetricVolume_le_exp_mul_of_local_ricci_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    {J I : Set ℝ} (F : RicciFlow n M J) (hI : Convex ℝ I) (hIJ : I ⊆ J)
    {U V : Set M} (hU : IsOpen U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    {K L s t : ℝ} (hK : 0 ≤ K) (hs : s ∈ I) (ht : t ∈ I) (hL : |s - t| ≤ L)
    (hRic : ∀ tau ∈ I, ∀ x ∈ U, ∀ w : TangentSpace (𝓡 n) x,
      |(F.connection tau).ricci x w w| ≤ K * (F.metric tau).inner x w w) :
    calibratedMetricVolume (F.metric s) V ≤ ENNReal.ofReal (Real.exp (K * L)) ^ n *
      calibratedMetricVolume (F.metric t) V := by
  let e := OpenPartialHomeomorph.ofSet U hU
  have hnorm (x : M) (hx : x ∈ U) (w : TangentSpace (𝓡 n) x) :
      (F.metric s).tangentNorm x w ≤ Real.exp (K * L) * (F.metric t).tangentNorm x w := by
    calc
      _ ≤ Real.exp (K * |s - t|) * (F.metric t).tangentNorm x w :=
        F.tangentNorm_le_exp_of_ricci_bound hI hIJ x w K
          (fun tau htau => hRic tau htau x hx w) ht hs
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL hK)) (Real.sqrt_nonneg _)
  have hb := calibratedMetricVolume_image_le_of_local_tangentNorm_le
    (F.metric t) (F.metric s) e (show ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source from
      contMDiffOn_id) (Real.exp_pos (K * L)) (fun x hx w => by
        change (F.metric s).tangentNorm x (mfderiv (𝓡 n) (𝓡 n) id x w) ≤ _
        rw [mfderiv_id, ContinuousLinearMap.id_apply]
        exact hnorm x hx w) hV hVU
  change calibratedMetricVolume (F.metric s) (id '' V) ≤ _ at hb
  simpa only [image_id] using hb

end PoincareMT.M34
