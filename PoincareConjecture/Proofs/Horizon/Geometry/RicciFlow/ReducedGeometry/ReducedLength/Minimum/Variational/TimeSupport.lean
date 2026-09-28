import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.AncientAction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Ancient

set_option autoImplicit false

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variational

noncomputable def stationaryTimeSupport (R : ℝ → ℝ) (τ m u : ℝ) : ℝ :=
  (2 * Real.sqrt τ * m + ∫ r in τ..u, Real.sqrt r * R r) / (2 * Real.sqrt u)

theorem stationaryTimeSupport_self (R : ℝ → ℝ) {τ : ℝ} (hτ : 0 < τ) (m : ℝ) :
    stationaryTimeSupport R τ m τ = m := by
  simp only [stationaryTimeSupport, intervalIntegral.integral_same, add_zero]
  exact mul_div_cancel_left₀ m (by positivity)

theorem hasDerivAt_stationaryTimeSupport (R : ℝ → ℝ)
    (hR : ContinuousOn R (Ioi 0)) {τ : ℝ} (hτ : 0 < τ) (m : ℝ) :
    HasDerivAt (stationaryTimeSupport R τ m) (R τ / 2 - m / (2 * τ)) τ := by
  have hcont : ContinuousOn (fun r => Real.sqrt r * R r) (Ioi 0) :=
    Real.continuous_sqrt.continuousOn.mul hR
  have hint : HasDerivAt (fun u => ∫ r in τ..u, Real.sqrt r * R r)
      (Real.sqrt τ * R τ) τ :=
    intervalIntegral.integral_hasDerivAt_right (by simp)
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi τ hτ)
      (hcont.continuousAt (Ioi_mem_nhds hτ))
  have hd := ((hasDerivAt_const τ (2 * Real.sqrt τ * m)).add hint).div
    ((Real.hasDerivAt_sqrt hτ.ne').const_mul 2)
    (show 2 * Real.sqrt τ ≠ 0 by positivity)
  apply hd.congr_deriv
  simp only [Pi.add_apply, intervalIntegral.integral_same, add_zero, zero_add]
  have hs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.2 hτ).ne'
  have hsq := Real.sq_sqrt hτ.le
  generalize hsqrt : Real.sqrt τ = s at *
  rw [← hsq]
  field_simp

end PoincareConjecture.ReducedLengthMinimum.Variational

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

section Metric

private theorem intervalL2_cast_apply {E : Type*} [NormedAddCommGroup E]
    {a b c d : ℝ} (ha : a = c) (hb : b = d)
    (h : (IntervalL2 E a b : Type _) = (IntervalL2 E c d : Type _))
    (v : IntervalL2 E c d) (s : ℝ) : (h.mpr v) s = v s := by
  subst c
  subst d
  rfl

variable {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ConnectedSpace M]

theorem stationary_tail_square_integral (K : AncientKappaSolution 2 M) (q : M)
    {τ u : ℝ} (hτ : 0 ≤ τ) (hu : τ ≤ u) :
    (∫ s in Real.sqrt τ..Real.sqrt u,
      2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature q) =
      ∫ r in τ..u, Real.sqrt r * (K.flow.connection (0 - r)).scalarCurvature q := by
  have hle := Real.sqrt_le_sqrt hu
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt τ) (b := Real.sqrt u)
    (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
    (g := fun r => Real.sqrt r * (K.flow.connection (0 - r)).scalarCurvature q)
    (continuous_id.pow 2).continuousOn
    (fun s _ => by simpa using hasDerivAt_pow 2 s)
    (fun s hs => by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ).trans hs.1.le))
  rw [Real.sq_sqrt hτ, Real.sq_sqrt (hτ.trans hu)] at hchange
  rw [← hchange]
  apply intervalIntegral.integral_congr_Ioo_of_le hle
  intro s hs
  simp only [Function.comp_apply, Real.sqrt_sq ((Real.sqrt_nonneg τ).trans hs.1.le)]
  ring

theorem reducedLength_le_stationary_extension (K : AncientKappaSolution 2 M)
    {τ u : ℝ} (hτ : 0 < τ) (hu : τ ≤ u)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (ht0 : t 0 = 0) (htend : t (Fin.last m) = Real.sqrt τ)
    (γ : ℝ → M) (hγ : Continuous γ) (x : Fin m → M)
    (hsrc : ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source)
    (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 2) (x i) (γ s) = extChartAt (𝓡 2) (x i) (γ (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r) :
    2 * Real.sqrt u * reducedLength K.flow 0 (γ 0) (γ (Real.sqrt τ)) u ≤
      (∑ i, ((∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric K.flow 0 (x i) (s, γ s) (w i s) (w i s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (γ s))) +
      ∫ r in τ..u, Real.sqrt r * (K.flow.connection (0 - r)).scalarCurvature (γ (Real.sqrt τ)) := by
  classical
  let c := Real.sqrt τ
  let q := γ c
  let δ : ℝ → M := fun s => γ (min s c)
  let t' : Fin (m + 2) → ℝ := Fin.snoc t (Real.sqrt u)
  let x' : Fin (m + 1) → M := Fin.snoc x q
  have hδ : Continuous δ := hγ.comp (continuous_id.min continuous_const)
  have hδleft (s : ℝ) (hs : s ≤ c) : δ s = γ s := by simp only [δ, min_eq_left hs]
  have hδright (s : ℝ) (hs : c ≤ s) : δ s = q := by simp only [δ, q, min_eq_right hs]
  have ht' : Monotone t' := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [t', Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, htend] using
        Real.sqrt_le_sqrt hu
    · simpa only [t', Fin.succ_castSucc, Fin.snoc_castSucc] using
        ht (Fin.castSucc_le_succ j)
  have hleft (i : Fin m) : t i.castSucc ≤ c := by
    change t i.castSucc ≤ Real.sqrt τ
    rw [← htend]
    exact ht (Fin.le_last _)
  have hright (i : Fin m) : t i.succ ≤ c := by
    change t i.succ ≤ Real.sqrt τ
    rw [← htend]
    exact ht (Fin.le_last _)
  let w' (i : Fin (m + 1)) :
      IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t' i.castSucc) (t' i.succ) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact 0
    · have h1 : t' j.castSucc.castSucc = t j.castSucc := Fin.snoc_castSucc ..
      have h2 : t' j.castSucc.succ = t j.succ := by
        rw [Fin.succ_castSucc]
        exact Fin.snoc_castSucc ..
      exact (show (IntervalL2 (EuclideanSpace ℝ (Fin 2))
        (t' j.castSucc.castSucc) (t' j.castSucc.succ) : Type _) =
        (IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t j.castSucc) (t j.succ) : Type _)
        from by rw [h1, h2]).mpr (w j)
  have hhead (i : Fin m) (s : ℝ) : w' i.castSucc s = w i s := by
    simp only [w', Fin.lastCases_castSucc]
    exact intervalL2_cast_apply (Fin.snoc_castSucc ..)
      (by rw [Fin.succ_castSucc]; exact Fin.snoc_castSucc ..) _ (w i) s
  have hlast : (w' (Fin.last m) : ℝ → EuclideanSpace ℝ (Fin 2))
      =ᵐ[volume.restrict (Icc c (Real.sqrt u))] 0 := by
    have hz := Lp.coeFn_zero (EuclideanSpace ℝ (Fin 2)) 2
      (volume.restrict (Icc (t' (Fin.last m).castSucc) (t' (Fin.last m).succ)))
    have hwzero : w' (Fin.last m) = 0 := by simp only [w', Fin.lastCases_last]
    rw [← hwzero] at hz
    simpa only [t', Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, htend, c] using hz
  have hsrc' (i : Fin (m + 1)) : MapsTo δ (Icc (t' i.castSucc) (t' i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x' i)).source := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro s hs
      simp only [t', Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, htend] at hs
      simpa only [x', Fin.snoc_last, hδright s hs.1] using mem_chart_source _ q
    · intro s hs
      simp only [t', Fin.succ_castSucc, Fin.snoc_castSucc] at hs
      have hj := hsrc j hs
      simpa only [x', Fin.snoc_castSucc, hδleft s (hs.2.trans (hright j))] using hj
  have hprimitive' (i : Fin (m + 1)) (s : ℝ) (hs : s ∈ Icc (t' i.castSucc) (t' i.succ)) :
      extChartAt (𝓡 2) (x' i) (δ s) = extChartAt (𝓡 2) (x' i) (δ (t' i.castSucc)) +
        ∫ r in t' i.castSucc..s, w' i r := by
    revert s hs
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro s hs
      simp only [t', Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, htend] at hs ⊢
      have hz : (∫ r in c..s, w' (Fin.last m) r) = 0 := by
        calc
          _ = ∫ r in c..s, (0 : EuclideanSpace ℝ (Fin 2)) := by
            apply intervalIntegral.integral_congr_ae_restrict
            rw [uIoc_of_le hs.1]
            exact ae_mono (Measure.restrict_mono
              (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hs.2)) le_rfl) hlast
          _ = 0 := by simp
      change _ = _ + ∫ r in c..s, w' (Fin.last m) r
      rw [hz, add_zero, hδright s hs.1, hδright c le_rfl]
    · intro s hs
      simp only [t', Fin.succ_castSucc, Fin.snoc_castSucc] at hs ⊢
      simpa only [x', Fin.snoc_castSucc, hhead, hδleft s (hs.2.trans (hright j)),
        hδleft (t j.castSucc) (hleft j)] using hprimitive j s hs
  have h := K.reducedLength_le_finite_chart_action (hτ.trans_le hu) t' ht'
    (by simpa only [t', Fin.snoc_apply_zero] using ht0)
    (by simp only [t', Fin.snoc_last]) δ hδ.continuousOn x' hsrc' w' hprimitive'
  have hδ0 : δ 0 = γ 0 := hδleft 0 (Real.sqrt_nonneg τ)
  have hδend : δ (Real.sqrt u) = γ (Real.sqrt τ) := hδright _ (Real.sqrt_le_sqrt hu)
  rw [hδ0, hδend, Fin.sum_univ_castSucc] at h
  have hkin : (∫ s in c..Real.sqrt u,
      regularizedChartMetric K.flow 0 q (s, δ s)
        (w' (Fin.last m) s) (w' (Fin.last m) s)) = 0 := by
    calc
      _ = ∫ s in c..Real.sqrt u, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (Real.sqrt_le_sqrt hu)]
        filter_upwards [ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) hlast]
          with s hs
        simp only [hs, Pi.zero_apply, map_zero]
      _ = 0 := by simp
  have htail : (∫ s in c..Real.sqrt u,
      2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (δ s)) =
      ∫ r in τ..u, Real.sqrt r * (K.flow.connection (0 - r)).scalarCurvature q := by
    rw [← K.stationary_tail_square_integral q hτ.le hu]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (Real.sqrt_le_sqrt hu)]
    intro s hs
    dsimp only
    rw [hδright s hs.1]
  simp only [t', x', Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last,
    Fin.snoc_last, htend, hhead] at h
  have hpieces (i : Fin m) :
      (∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric K.flow 0 (x i) (s, δ s) (w i s) (w i s)) +
        (∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (δ s)) =
      (∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric K.flow 0 (x i) (s, γ s) (w i s) (w i s)) +
        (∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (γ s)) := by
    congr 1 <;> apply intervalIntegral.integral_congr <;>
      rw [uIcc_of_le (ht (Fin.castSucc_le_succ i))] <;>
      intro s hs <;> dsimp only <;> rw [hδleft s (hs.2.trans (hright i))]
  dsimp only [c] at hkin htail
  simpa only [hpieces, hkin, htail, zero_add, q, c] using h

end Metric

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_stationary_time_comparison (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ q : M, reducedLength K.flow 0 p q τ = K.spatialReducedLengthInfimum p τ ∧
      ∀ u : ℝ, τ ≤ u → K.spatialReducedLengthInfimum p u ≤
        stationaryTimeSupport (fun r => (K.flow.connection (0 - r)).scalarCurvature q)
          τ (K.spatialReducedLengthInfimum p τ) u := by
  let : MetricSpace M := referenceMetricSpace (K.flow.metric 0)
  obtain ⟨γ, m, t, x, Q, w, hγ, hγ0, ht, ht0, htend, hQ, hprimitive, hbound⟩ :=
    K.exists_spatial_minimizing_weak_action p hτ
  have hsrc (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source :=
    fun s hs => (hQ i).2.2 (interior_subset ((hQ i).2.1 (mem_image_of_mem γ hs)))
  have hmin := K.reducedLength_le_finite_chart_action hτ t ht ht0 htend
    γ hγ.continuousOn x hsrc w hprimitive
  have hq : reducedLength K.flow 0 p (γ (Real.sqrt τ)) τ =
      K.spatialReducedLengthInfimum p τ := by
    apply le_antisymm _ (K.spatialReducedLengthInfimum_le p _ τ)
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * Real.sqrt τ by positivity)).mp
    simpa only [hγ0] using hmin.trans hbound
  refine ⟨γ (Real.sqrt τ), hq, ?_⟩
  intro u hu
  have hu' : 0 < u := hτ.trans_le hu
  have hupos : 0 < 2 * Real.sqrt u := by positivity
  apply (le_div_iff₀ hupos).mpr
  have hext := K.reducedLength_le_stationary_extension hτ hu t ht ht0 htend
    γ hγ x hsrc w hprimitive
  have hinf := mul_le_mul_of_nonneg_left
    (K.spatialReducedLengthInfimum_le p (γ (Real.sqrt τ)) u) hupos.le
  have hle := hinf.trans (by simpa only [hγ0] using hext)
  simpa only [stationaryTimeSupport, mul_comm] using
    hle.trans (_root_.add_le_add hbound le_rfl)

theorem exists_right_time_upper_support (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) :
    ∃ (q : M) (b : ℝ → ℝ),
      reducedLength K.flow 0 p q τ = K.spatialReducedLengthInfimum p τ ∧
      b τ = K.spatialReducedLengthInfimum p τ ∧
      HasDerivAt b ((K.flow.connection (0 - τ)).scalarCurvature q / 2 -
        K.spatialReducedLengthInfimum p τ / (2 * τ)) τ ∧
      ∀ u : ℝ, τ ≤ u → K.spatialReducedLengthInfimum p u ≤ b u := by
  obtain ⟨q, hq, hsupport⟩ := K.exists_stationary_time_comparison p hτ
  have hR : ContinuousOn (fun r => (K.flow.connection (0 - r)).scalarCurvature q)
      (Ioi (0 : ℝ)) :=
    (K.flow.continuousOn_scalarCurvature_ancient_surface q).comp
      (continuous_const.sub continuous_id).continuousOn
      (fun r hr => show 0 - r ∈ Iic 0 from by
        change 0 < r at hr
        exact sub_nonpos.mpr hr.le)
  refine ⟨q, stationaryTimeSupport _ τ (K.spatialReducedLengthInfimum p τ), hq,
    stationaryTimeSupport_self _ hτ _, ?_, hsupport⟩
  exact hasDerivAt_stationaryTimeSupport _ hR hτ _

end PoincareConjecture.AncientKappaSolution
