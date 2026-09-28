import PoincareConjecture.Proofs.M47.BlowupControlsCapCoreRadius
import PoincareConjecture.Proofs.M34.Standard.CapBallVolumeReference

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_cap_image_core_volume_tolerance {g : RiemannianMetric 3 M}
    (N : CapCertificate g) (hcomplete : MetricComplete g)
    (hRic : ∀ x, ∀ w : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x w w) :
    ∃ Lambda : ℝ, 1 < Lambda ∧ ∃ nu : ℝ, 0 < nu ∧
      ∃ b' : ℝ, N.cap_constant⁻¹ < b' ∧
      ∀ {X : Type v} [TopologicalSpace X]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
        [MeasurableSpace X] [BorelSpace X] [T3Space X] [SecondCountableTopology X]
        (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
        (e : OpenPartialHomeomorph M X),
      ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source →
      ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target → N.carrier ⊆ e.source →
      (∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
        h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
          Lambda * g.tangentNorm x w) →
      (∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
        g.tangentNorm x w ≤
          Lambda * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w)) →
      (∀ x ∈ N.carrier, N.connection.scalarCurvature x ≤ D.scalarCurvature (e x) + nu) →
      ∀ y ∈ N.core, ∀ r : ℝ, 0 < r →
        BddAbove (D.scalarCurvature '' h.ball (e y) r) →
        scalarCurvatureSupOn h D (h.ball (e y) r) = r⁻¹ ^ 2 →
        ENNReal.ofReal (b' * r ^ 3) ≤ calibratedMetricVolume h (h.ball (e y) r) := by
  obtain ⟨b0, hb0, hbase⟩ := N.core_ball_volume_lower
  have hb0pos : 0 < b0 := (inv_pos.mpr N.cap_constant_pos).trans hb0
  let b' := (N.cap_constant⁻¹ + b0) / 2
  have hb' : N.cap_constant⁻¹ < b' := by dsimp [b']; linarith
  have hb'pos : 0 < b' := (inv_pos.mpr N.cap_constant_pos).trans hb'
  have hb'b0 : b' < b0 := by dsimp [b']; linarith
  have hnear : ∀ᶠ L : ℝ in 𝓝 1, b' * L ^ 6 < b0 :=
    (continuousAt_const.mul (continuousAt_id.pow 6)).eventually_lt continuousAt_const
      (by simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, one_pow, mul_one] using hb'b0)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let Lambda := 1 + delta / 2
  have hLambda : 1 < Lambda := by dsimp [Lambda]; linarith
  have hLpos : 0 < Lambda := zero_lt_one.trans hLambda
  have hcoeff : b' * Lambda ^ 6 ≤ b0 := by
    refine (hball ?_).le
    change dist Lambda 1 < delta
    rw [Real.dist_eq]
    dsimp only [Lambda]
    rw [add_sub_cancel_left, abs_of_pos (half_pos hdelta)]
    linarith
  obtain ⟨nu, hnu, hradius⟩ := exists_cap_image_core_radius_tolerance N hLambda
  refine ⟨Lambda, hLambda, nu, hnu, b', hb', ?_⟩
  intro X _ _ _ _ _ _ _ h D e hf hi hsource hupper hlower hscalar y hy r hr hb hnorm
  have hrr := hradius h D e hf hsource hupper hscalar y hy r hr hb hnorm
  let r0 := N.core_radius y
  let s := r / Lambda
  have hr0 : 0 < r0 := N.core_radius_pos y hy
  have hs : 0 < s := div_pos hr hLpos
  have hsr0 : s ≤ r0 := (div_le_iff₀ hLpos).mpr (by simpa only [mul_comm] using hrr)
  have hsourceSmall : g.ball y s ⊆ e.source := by
    intro z hz
    have hz0 : z ∈ g.ball y r0 :=
      (show g.edist y z < ENNReal.ofReal s from hz).trans_le
        (ENNReal.ofReal_le_ofReal hsr0)
    exact hsource (N.core_ball_subset y hy (subset_closure hz0))
  have hbase' : ENNReal.ofReal b0 * ENNReal.ofReal r0 ^ 3 ≤
      calibratedMetricVolume g (g.ball y r0) := by
    rw [← ENNReal.ofReal_pow hr0.le, ← ENNReal.ofReal_mul hb0pos.le]
    exact hbase y hy
  have hsmall : ENNReal.ofReal (b0 * s ^ 3) ≤
      calibratedMetricVolume g (g.ball y s) := by
    have hBG := g.calibrated_small_ball_volume_lower_of_nonnegative_ricci
      N.connection (by norm_num : 1 ≤ 3) hcomplete hRic y hs hr0 hsr0 hbase'
    simpa only [← ENNReal.ofReal_pow hs.le, ← ENNReal.ofReal_mul hb0pos.le] using hBG
  have hvolume : calibratedMetricVolume g (g.ball y s) ≤
      ENNReal.ofReal Lambda ^ 3 * calibratedMetricVolume h (h.ball (e y) r) :=
    M34.calibrated_ball_volume_le_mul_of_tangent_bounds g h e hf hi hLpos hLpos
      hupper hlower hsourceSmall (by dsimp [s]; rw [mul_div_cancel₀ _ hLpos.ne'])
  have hweighted := hsmall.trans hvolume
  rw [← ENNReal.ofReal_pow hLpos.le] at hweighted
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (pow_pos hLpos 3)).ne'
    ENNReal.ofReal_ne_top).mp
  have hreal : Lambda ^ 3 * (b' * r ^ 3) ≤ b0 * s ^ 3 := by
    calc
      _ = (b' * Lambda ^ 6) * s ^ 3 := by
        dsimp [s]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hs.le 3)
  calc
    ENNReal.ofReal (Lambda ^ 3) * ENNReal.ofReal (b' * r ^ 3) =
        ENNReal.ofReal (Lambda ^ 3 * (b' * r ^ 3)) :=
      (ENNReal.ofReal_mul (pow_nonneg hLpos.le 3)).symm
    _ ≤ ENNReal.ofReal (b0 * s ^ 3) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ _ := hweighted

end PoincareConjecture.M47
