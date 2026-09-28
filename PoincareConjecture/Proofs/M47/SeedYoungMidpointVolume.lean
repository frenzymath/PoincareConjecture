import PoincareConjecture.Proofs.M47.SeedMidpointVolume

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem seed_midpoint_volume_of_exponential_metric_bounds
    (g h : RiemannianMetric 3 M) (q : M) {R B V : ℝ} (hR : 0 < R)
    (hupper : ∀ x : M, ∀ w : TangentSpace (𝓡 3) x,
      h.inner x w w ≤ g.inner x w w)
    (hlower : ∀ x ∈ closure (g.ball q R), ∀ w : TangentSpace (𝓡 3) x,
      Real.exp (-4 * B) * g.inner x w w ≤ h.inner x w w)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume g (g.ball q (R / 2))) :
    ENNReal.ofReal (Real.exp (-6 * B) * V) ≤
      calibratedMetricVolume h (h.ball q (R / 2)) := by
  have hopen (r : ℝ) : IsOpen (g.ball q r) := by
    let : PseudoEMetricSpace M := g.comparisonPseudoEMetric
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let e := OpenPartialHomeomorph.ofSet (g.ball q R) (hopen R)
  have hcancel : Real.exp (4 * B) * Real.exp (-4 * B) = 1 := by
    rw [← Real.exp_add, show 4 * B + -4 * B = 0 by ring, Real.exp_zero]
  have hsquare : Real.exp (2 * B) ^ 2 = Real.exp (4 * B) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnorm : ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
      g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
        Real.exp (2 * B) * h.tangentNorm x w := by
    intro x hx w
    change g.tangentNorm x (mfderiv (𝓡 3) (𝓡 3) id x w) ≤ _
    rw [mfderiv_id, ContinuousLinearMap.id_apply]
    have hh : 0 ≤ h.inner x w w := by
      by_cases hw : w = 0
      · simp [hw]
      · exact (h.pos x w hw).le
    have hquad := mul_le_mul_of_nonneg_left (hlower x (subset_closure hx) w)
      (Real.exp_pos (4 * B)).le
    rw [← mul_assoc, hcancel, one_mul] at hquad
    change Real.sqrt (g.inner x w w) ≤ Real.exp (2 * B) * Real.sqrt (h.inner x w w)
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hh, hsquare] using hquad
  have hsub : g.ball q (R / 2) ⊆ e.source := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (half_le_self hR.le))
  have hvol := M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le h g e
    (show ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source from contMDiffOn_id)
    (Real.exp_pos (2 * B)) hnorm (hopen (R / 2)).measurableSet hsub
  change calibratedMetricVolume g (id '' g.ball q (R / 2)) ≤ _ at hvol
  simp only [image_id] at hvol
  have hball : g.ball q (R / 2) ⊆ h.ball q (R / 2) := by
    have hb := g.ball_subset_ball_of_tangentNorm_le h q (R / 2) 1 zero_lt_one
      (fun x _hx w => by
        change Real.sqrt (h.inner x w w) ≤ 1 * Real.sqrt (g.inner x w w)
        simpa only [one_mul] using Real.sqrt_le_sqrt (hupper x w))
    simpa only [one_mul] using hb
  have hbound := hvolume.trans (hvol.trans (mul_le_mul' le_rfl (measure_mono hball)))
  have hreal : Real.exp (-6 * B) * Real.exp (2 * B) ^ 3 = 1 := by
    rw [pow_succ, pow_two]
    simp only [← Real.exp_add]
    rw [show -6 * B + (2 * B + 2 * B + 2 * B) = 0 by ring, Real.exp_zero]
  have hcancelVolume : ENNReal.ofReal (Real.exp (-6 * B)) *
      ENNReal.ofReal (Real.exp (2 * B)) ^ 3 = 1 := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos (2 * B)).le,
      ← ENNReal.ofReal_mul (Real.exp_pos (-6 * B)).le, hreal, ENNReal.ofReal_one]
  rw [ENNReal.ofReal_mul (Real.exp_pos (-6 * B)).le]
  exact (mul_le_mul_right hbound _).trans_eq
    (by rw [← mul_assoc, hcancelVolume, one_mul])

theorem seed_young_midpoint_volume
    {J : Set ℝ} (G : RicciFlow 3 M J) {b v d B R V : ℝ}
    (q : M) (hd : 0 < d) (hB : 0 ≤ B) (hR : 0 < R)
    (hv : 0 ≤ v) (hvd : v ≤ d / 2) (hJ : Icc b (b + v) ⊆ J)
    (hsec : ∀ s ∈ Icc b (b + v), ∀ x : M, ∀ w z : TangentSpace (𝓡 3) x,
      0 ≤ (G.connection s).curvatureTensor x w z w z)
    (hscalar : ∀ x ∈ closure ((G.metric b).ball q R), ∀ s ∈ Icc b (b + v),
      (G.connection s).scalarCurvature x ≤ 8 * B / d)
    (hvolume : ENNReal.ofReal V ≤
      calibratedMetricVolume (G.metric b) ((G.metric b).ball q (R / 2))) :
    ENNReal.ofReal (Real.exp (-6 * B) * V) ≤
      calibratedMetricVolume (G.metric (b + v / 2))
        ((G.metric (b + v / 2)).ball q (R / 2)) := by
  have ht : b + v / 2 ∈ Icc b (b + v) := ⟨by linarith, by linarith⟩
  have hsub : Icc b (b + v / 2) ⊆ Icc b (b + v) := Icc_subset_Icc le_rfl ht.2
  apply seed_midpoint_volume_of_exponential_metric_bounds
    (G.metric b) (G.metric (b + v / 2)) q hR
    (fun x w => PoincareConjecture.M47.jointSeed_metric_upper_of_nonnegative_sectional
      G ht.1 (hsub.trans hJ) (fun s hs => hsec s (hsub hs)) x w) _ hvolume
  intro x hx w
  have hlocal := PoincareConjecture.M47.jointSeed_metric_lower_of_scalar_bound
    G ht.1 (hsub.trans hJ) x (fun s hs => hsec s (hsub hs) x)
    (fun s hs => hscalar x hx s (hsub hs)) w
  have hexponent : -2 * (8 * B / d) * (b + v / 2 - b) = (-8 * B * v) / d := by ring
  have htime : -4 * B ≤ -2 * (8 * B / d) * (b + v / 2 - b) := by
    rw [hexponent]
    apply (le_div_iff₀ hd).mpr
    have h := mul_le_mul_of_nonneg_left hvd hB
    nlinarith only [h]
  have hnonneg : 0 ≤ (G.metric b).inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((G.metric b).pos x w hw).le
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htime) hnonneg).trans hlocal

end PoincareConjecture.Proofs.M47
