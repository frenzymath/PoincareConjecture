import PoincareConjecture.Proofs.M47.BlowupControlsCapScalarSup

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M47

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem exists_cap_geometric_margin {g : RiemannianMetric 3 M} (N : CapCertificate g) :
    ∃ Lambda : ℝ, 1 < Lambda ∧ ∃ nu : ℝ, 0 < nu ∧
      ∀ s : ℝ, |s - scalarCurvatureSupOn g N.connection N.carrier| ≤ nu →
        0 < s ∧
        ENNReal.ofReal Lambda * intrinsicDiameter g N.carrier <
          ENNReal.ofReal (N.cap_constant * s ^ (-1 / 2 : ℝ)) ∧
        ENNReal.ofReal Lambda ^ 3 * calibratedMetricVolume g N.carrier <
          ENNReal.ofReal N.cap_constant * ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) := by
  let S := scalarCurvatureSupOn g N.connection N.carrier
  let D := intrinsicDiameter g N.carrier
  let V := calibratedMetricVolume g N.carrier
  have hne : N.carrier.Nonempty := ⟨N.end_neck.center, N.end_neck_subset
    (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)⟩
  have hS : 0 < S := N.scalarSup_pos_on_subset subset_rfl hne
  have hD : D < ENNReal.ofReal (N.cap_constant * S ^ (-1 / 2 : ℝ)) :=
    N.intrinsic_diameter_bound
  have hV : V < ENNReal.ofReal (N.cap_constant * S ^ (-3 / 2 : ℝ)) := by
    simpa only [ENNReal.ofReal_mul N.cap_constant_pos.le] using N.volume_bound
  have hDfinite : D ≠ ⊤ := ne_of_lt (hD.trans_le le_top)
  have hVfinite : V ≠ ⊤ := ne_of_lt (hV.trans_le le_top)
  have hDreal : D.toReal < N.cap_constant * S ^ (-1 / 2 : ℝ) := by
    simpa only [ENNReal.toReal_ofReal (mul_pos N.cap_constant_pos
      (Real.rpow_pos_of_pos hS _)).le] using
      (ENNReal.toReal_lt_toReal hDfinite ENNReal.ofReal_ne_top).mpr hD
  have hVreal : V.toReal < N.cap_constant * S ^ (-3 / 2 : ℝ) := by
    simpa only [ENNReal.toReal_ofReal (mul_pos N.cap_constant_pos
      (Real.rpow_pos_of_pos hS _)).le] using
      (ENNReal.toReal_lt_toReal hVfinite ENNReal.ofReal_ne_top).mpr hV
  have hrightD : ContinuousAt (fun z : ℝ × ℝ =>
      N.cap_constant * z.2 ^ (-1 / 2 : ℝ)) (1, S) :=
    continuousAt_const.mul (continuous_snd.continuousAt.rpow_const (Or.inl hS.ne'))
  have hrightV : ContinuousAt (fun z : ℝ × ℝ =>
      N.cap_constant * z.2 ^ (-3 / 2 : ℝ)) (1, S) :=
    continuousAt_const.mul (continuous_snd.continuousAt.rpow_const (Or.inl hS.ne'))
  have hnearD : ∀ᶠ z : ℝ × ℝ in 𝓝 (1, S),
      z.1 * D.toReal < N.cap_constant * z.2 ^ (-1 / 2 : ℝ) :=
    (continuous_fst.continuousAt.mul continuousAt_const).eventually_lt hrightD
      (by simpa only [Pi.mul_apply, Prod.fst, one_mul] using hDreal)
  have hnearV : ∀ᶠ z : ℝ × ℝ in 𝓝 (1, S),
      z.1 ^ 3 * V.toReal < N.cap_constant * z.2 ^ (-3 / 2 : ℝ) :=
    ((continuous_fst.pow 3).continuousAt.mul continuousAt_const).eventually_lt hrightV
      (by simpa only [Pi.mul_apply, Pi.pow_apply, Prod.fst, one_pow, one_mul] using hVreal)
  have hnearS : ∀ᶠ z : ℝ × ℝ in 𝓝 (1, S), 0 < z.2 :=
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds hS)
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp
    (hnearS.and (hnearD.and hnearV))
  let nu := radius / 2
  have hnu : 0 < nu := half_pos hradius
  have hnuRadius : nu < radius := by dsimp [nu]; linarith
  have hLambda : 0 < 1 + nu := by linarith
  refine ⟨1 + nu, by linarith, nu, hnu, ?_⟩
  intro s hclose
  have hdistance : dist (1 + nu, s) (1, S) ≤ nu := by
    rw [Prod.dist_eq]
    apply max_le
    · simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hnu] using le_refl nu
    · exact hclose
  obtain ⟨hs, hd, hv⟩ := hball (hdistance.trans_lt hnuRadius)
  refine ⟨hs, ?_, ?_⟩
  · have h := (ENNReal.ofReal_lt_ofReal_iff
      (mul_pos N.cap_constant_pos (Real.rpow_pos_of_pos hs _))).mpr hd
    rw [ENNReal.ofReal_mul hLambda.le, ENNReal.ofReal_toReal hDfinite] at h
    exact h
  · have h := (ENNReal.ofReal_lt_ofReal_iff
      (mul_pos N.cap_constant_pos (Real.rpow_pos_of_pos hs _))).mpr hv
    rw [ENNReal.ofReal_mul (pow_nonneg hLambda.le 3), ENNReal.ofReal_pow hLambda.le,
      ENNReal.ofReal_toReal hVfinite, ENNReal.ofReal_mul N.cap_constant_pos.le] at h
    exact h

end PoincareConjecture.M47
