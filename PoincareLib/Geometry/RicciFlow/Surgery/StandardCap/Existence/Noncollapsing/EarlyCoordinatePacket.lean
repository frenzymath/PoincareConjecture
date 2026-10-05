import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.UniformInitialCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.EarlySlabComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.CoordinateMetricBounds

/-!
# Fixed-slab coordinate volume and speed bounds

One uniform coordinate packet supplies a positive image volume and a
differential bound at every time in the chosen early slab. These constants
are chosen before the late query time and the reduced-length center.
Source: Morgan-Tian Proposition 12.13, pp. 304-306.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareMT.M34

/-- Uniform early-slab charts retain their actual image volume and bound
every tangent differential (Proposition 12.13, pp. 304-306). -/
theorem partialFlow_early_coordinate_packet {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (P : RicciFlowCurvatureTheory.{0})
    {T : ℝ} (hT : T ∈ Ico 0 F.lifetime) :
    ∃ delta d V : ℝ, 0 < delta ∧ 0 < d ∧ 0 < V ∧ ∀ q : StandardCapSpace,
      ∃ f : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞,
        f 0 = q ∧ Metric.ball 0 delta ⊆ f.source ∧
        ∀ t ∈ Icc 0 T,
          (∀ z ∈ Metric.ball 0 delta, ∀ w : StandardCapSpace,
            (F.flow.metric t).tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z w) ≤
              d * ‖w‖) ∧
          ENNReal.ofReal V ≤ calibratedMetricVolume (F.flow.metric t)
            (f '' Metric.ball 0 delta) := by
  obtain ⟨delta, b, v0, hdelta, hb, hv0, hcharts⟩ :=
    uniform_initial_coordinate_volume g0.cylindrical_end
  obtain ⟨c, hc, hnorm⟩ := partialFlow_uniform_tangentNorm_comparison F P hT
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  let V := v0 * delta ^ 3 / c ^ 3
  have hV : 0 < V := div_pos (mul_pos hv0 (pow_pos hdelta _)) (pow_pos hcpos _)
  refine ⟨delta, c * Real.sqrt b, V, hdelta,
    mul_pos hcpos (Real.sqrt_pos.mpr hb), hV, ?_⟩
  intro q
  obtain ⟨f, hf0, hsource, hcoeff, hvolume⟩ := hcharts q
  have hsub : Metric.ball (0 : StandardCapSpace) delta ⊆ Metric.ball 0 (2 * delta) :=
    Metric.ball_subset_ball (by linarith)
  refine ⟨f, hf0, hsub.trans hsource, fun t ht => ⟨?_, ?_⟩⟩
  · intro z hz w
    have h0 := tangentNorm_mfderiv_le_of_pullbackMetricForm_norm_le g0.metric f z
      hb.le (hcoeff z (hsub hz)) w
    calc
      _ ≤ c * g0.metric.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z w) :=
        (hnorm t ht (f z) (mfderiv (𝓡 3) (𝓡 3) f z w)).2
      _ ≤ c * (Real.sqrt b * ‖w‖) := mul_le_mul_of_nonneg_left h0 hcpos.le
      _ = _ := (mul_assoc _ _ _).symm
  · have hmeasure := (hvolume delta ⟨hdelta, le_rfl⟩).trans
      (calibratedMetricVolume_le_of_tangentNorm_le (F.flow.metric t) g0.metric hcpos
        (fun x w => (hnorm t ht x w).1) (f '' Metric.ball 0 delta))
    change ENNReal.ofReal (v0 * delta ^ 3 / c ^ 3) ≤ _
    rw [ENNReal.ofReal_div_of_pos (pow_pos hcpos 3)]
    apply (ENNReal.div_le_iff
      (ENNReal.ofReal_pos.mpr (pow_pos hcpos 3)).ne' ENNReal.ofReal_ne_top).mpr
    simpa only [ENNReal.ofReal_pow hcpos.le, mul_comm] using hmeasure

end PoincareMT.M34
