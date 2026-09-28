import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceInitialModulus
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicL2UniformLimit
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory AddCircle
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)

theorem exists_closed_uniform_embeddedCurvature_limit
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {K R J m0 V0 : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J)
    (hBounds : CurveEvolutionAmbientBounds F K K K) (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    (c : ℕ → ℝ → ℝ → M) (hc : ∀ j, M62ShrinkingCurve F (c j))
    (v0 : ℕ → ℝ) (hv0 : ∀ j, v0 j ∈ Icc m0 V0)
    (hinitial : ∀ j x, curveSpeed F (c j) a x = v0 j)
    (hcurv : ∀ j t, t ∈ Ioo a b → ∀ x, m62CurvatureSquared F (c j) t x ≤ R)
    (hjet : ∀ j t, t ∈ Ioo a b → ∀ x,
      (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F (c j) 1 t x) ≤
        J / Real.sqrt (t - a))
    (H : ℕ → ℝ → X) (h0 : X)
    (hrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ, H j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x))
    (hstart : Tendsto (fun j => H j a) atTop (𝓝 h0)) :
    let _ : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
    (∀ t ∈ Ioc a b, CauchySeq (fun j => ContinuousMap.toLp 2 haarAddCircle ℝ (H j t))) →
    (∀ d ∈ Ioc a b, ∀ eps > 0, ∃ eta > 0, ∀ j s, s ∈ Icc d b →
      ∀ t ∈ Icc d b, |t - s| < eta → ‖H j t - H j s‖ < eps) →
    ∃ h : ℝ → X, ContinuousOn h (Icc a b) ∧ h a = h0 ∧
      TendstoUniformlyOn H h atTop (Icc a b) ∧
      ∀ eps > 0, ∃ d > 0, ∀ t ∈ Icc a b, t - a < d → ‖h t - h0‖ < eps := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  intro hL2 hequi
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hcont (j : ℕ) : ContinuousOn (H j) (Icc a b) := by
    obtain ⟨h, h1, h2, hdot, hh, _, _, _, hval, _⟩ :=
      exists_periodic_embeddedCurvature_restart_data F (c j) hab (hc j) he
    apply hh.congr
    intro t ht
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact (hrep j t ht x).trans (hval t ht x).symm
  obtain ⟨E1, E2, E3, ⟨hE1, hE2, hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  let V := V0 * Real.exp ((K + R) * (b - a))
  have hV : 0 ≤ V := mul_nonneg (hm0.le.trans hmV) (Real.exp_pos _).le
  have hspatial (d : ℝ) (hd : a < d) :
      ∃ C : ℝ≥0, ∀ j t, t ∈ Ioo d b →
        LipschitzWith C (fun x : ℝ => H j t (x : AddCircle curvePeriod)) := by
    let C := V * (E1 * (J / Real.sqrt (d - a)) + E2 * Real.sqrt R)
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨⟨C, hC⟩, ?_⟩
    intro j t ht
    have ht' : t ∈ Ioo a b := ⟨hd.trans ht.1, ht.2⟩
    have htclosed := Ioo_subset_Icc_self ht'
    have hreal : (fun x : ℝ => H j t (x : AddCircle curvePeriod)) =
        fun x => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t)
          (m62CurvatureVector F (c j) t x) : W) := funext (hrep j t htclosed)
    rw [hreal]
    apply lipschitzWith_of_nnnorm_deriv_le
    · intro x
      exact (hasDerivAt_embeddedCurvature_spatial F (c j) (hc j) he ht' x).differentiableAt
    · intro x
      have hbound := (embeddedCurvature_derivative_remainder_bounds F (c j) (hc j) he
        hK hK hK hBounds ht' x hE1 hE2 hE3
        (fun Y => (hE t htclosed (c j x t) Y 0 0).1)
        (fun Y Z => (hE t htclosed (c j x t) Y Z 0).2.1)
        (fun Y Z A => (hE t htclosed (c j x t) Y Z A).2.2)).1
      have hv := (curveSpeed_exp_bounds F (c j) (hc j) hBounds x
        (fun r hr => hcurv j r hr x) ha htclosed ht'.1.le).2
      rw [hinitial j x] at hv
      have hvV : curveSpeed F (c j) t x ≤ V := hv.trans (by
        apply mul_le_mul (hv0 j).2
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
            (sub_le_sub_right ht'.2.le a) (add_nonneg hK hR)))
          (Real.exp_pos _).le (hm0.le.trans hmV))
      have hk : m62Curvature F (c j) t x ≤ Real.sqrt R := by
        nlinarith only [curvature_sq F (c j) t x, hcurv j t ht' x,
          Real.sq_sqrt hR, Real.sqrt_nonneg R, curvature_nonneg F (c j) t x]
      have hJd : (F.metric t).tangentNorm (c j x t)
          (m63CurvatureJet F (c j) 1 t x) ≤ J / Real.sqrt (d - a) :=
        (hjet j t ht' x).trans (div_le_div_of_nonneg_left hJ
          (Real.sqrt_pos.mpr (sub_pos.mpr hd))
          (Real.sqrt_le_sqrt (sub_le_sub_right ht.1.le a)))
      change ‖deriv (fun y => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j y t)
          (m62CurvatureVector F (c j) t y) : W)) x‖ ≤ C
      apply hbound.trans
      dsimp only [C]
      gcongr
      exact add_nonneg
        (mul_nonneg hE1 (Real.sqrt_nonneg _))
        (mul_nonneg hE2 (curvature_nonneg F (c j) t x))
  have hLip (t : ℝ) (ht : t ∈ Ioc a b) :
      ∃ C : ℝ≥0, ∀ j, LipschitzWith C (fun x : ℝ => H j t (x : AddCircle curvePeriod)) := by
    let d := (a + t) / 2
    have had : a < d := by dsimp only [d]; linarith [ht.1]
    have hdt : d < t := by dsimp only [d]; linarith [ht.1]
    have hdb : d < b := hdt.trans_le ht.2
    obtain ⟨C, hCbound⟩ := hspatial d had
    refine ⟨C, ?_⟩
    intro j
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hclosed : ContinuousOn (fun r =>
        ‖H j r (x : AddCircle curvePeriod) - H j r (y : AddCircle curvePeriod)‖)
        (Icc d b) :=
      (((ContinuousMap.evalCLM ℝ (x : AddCircle curvePeriod)).continuous.comp_continuousOn
        ((hcont j).mono (Icc_subset_Icc had.le le_rfl))).sub
        ((ContinuousMap.evalCLM ℝ (y : AddCircle curvePeriod)).continuous.comp_continuousOn
          ((hcont j).mono (Icc_subset_Icc had.le le_rfl)))).norm
    have hle : ∀ r ∈ Ioo d b,
        ‖H j r (x : AddCircle curvePeriod) - H j r (y : AddCircle curvePeriod)‖ ≤
          C * |x - y| := by
      intro r hr
      simpa only [dist_eq_norm, Real.norm_eq_abs] using (hCbound j r hr).dist_le_mul x y
    have hfinal := le_on_closure hle
      (by simpa only [closure_Ioo hdb.ne] using hclosed) continuousOn_const
      (show t ∈ closure (Ioo d b) by rw [closure_Ioo hdb.ne]; exact ⟨hdt.le, ht.2⟩)
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hfinal
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      ∃ z : X, Tendsto (fun j => H j t) atTop (𝓝 z) := by
    by_cases hta : t = a
    · subst t
      exact ⟨h0, hstart⟩
    · have hpos : t ∈ Ioc a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2⟩
      obtain ⟨C, hC⟩ := hLip t hpos
      exact cauchySeq_tendsto_of_complete
        (cauchySeq_of_cauchySeq_L2_of_lipschitz (H · t) (hL2 t hpos) hC)
  choose hsub hsubLimit using fun t : Icc a b => hpoint t t.property
  let h : ℝ → X := fun t => if ht : t ∈ Icc a b then hsub ⟨t, ht⟩ else 0
  have hlimit (t : ℝ) (ht : t ∈ Icc a b) : Tendsto (fun j => H j t) atTop (𝓝 (h t)) := by
    simpa only [h, dif_pos ht] using hsubLimit ⟨t, ht⟩
  have hzero : h a = h0 := tendsto_nhds_unique (hlimit a ha) hstart
  have hmodulus (eps : ℝ) (heps : 0 < eps) :
      ∃ d > 0, ∀ j t, t ∈ Icc a b → t - a < d → ‖H j t - H j a‖ < eps := by
    obtain ⟨d, hd, hmod⟩ := embeddedCurvature_uniform_initial_trace_on_compact_data
      F hab hcompact he hK hR hJ hBounds hm0 hmV hstart.isCompact_insert_range heps
    refine ⟨d, hd, ?_⟩
    intro j t ht htd
    exact hmod (c j) (hc j) (v0 j) (hv0 j) (hinitial j) (hcurv j) (hjet j)
      (H j) (hrep j) (mem_insert_of_mem _ (mem_range_self j)) t ht htd
  have hfull : Equicontinuous (fun j (t : Icc a b) => H j t) := by
    intro t
    apply Metric.equicontinuousAt_iff.mpr
    intro eps heps
    by_cases hta : (t : ℝ) = a
    · obtain ⟨d, hd, hmod⟩ := hmodulus eps heps
      refine ⟨d, hd, ?_⟩
      intro s hst j
      have hnear : (s : ℝ) - a < d := by
        simpa only [Subtype.dist_eq, Real.dist_eq, hta,
          abs_of_nonneg (sub_nonneg.mpr s.property.1)] using hst
      rw [dist_eq_norm, hta, norm_sub_rev]
      exact hmod j s s.property hnear
    · let d := (a + (t : ℝ)) / 2
      have hat : a < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm hta)
      have had : a < d := by dsimp only [d]; linarith
      have hdt : d < (t : ℝ) := by dsimp only [d]; linarith
      obtain ⟨eta, heta, hsmall⟩ := hequi d ⟨had, hdt.le.trans t.property.2⟩ eps heps
      refine ⟨min eta ((t : ℝ) - d), lt_min heta (sub_pos.mpr hdt), ?_⟩
      intro s hst j
      have hdist : |(s : ℝ) - (t : ℝ)| < min eta ((t : ℝ) - d) := hst
      have hsd : d ≤ (s : ℝ) := by
        have hleft := (abs_lt.mp (hdist.trans_le (min_le_right _ _))).1
        linarith
      rw [dist_eq_norm, norm_sub_rev]
      exact hsmall j t ⟨hdt.le, t.property.2⟩ s ⟨hsd, s.property.2⟩
        (hdist.trans_le (min_le_left _ _))
  have hrestricted : TendstoUniformly (fun j (t : Icc a b) => H j t)
      (fun t : Icc a b => h t) atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.mp
      ((hfull.tendsto_uniformFun_iff_pi atTop (fun t : Icc a b => h t)).mpr
        (tendsto_pi_nhds.mpr fun t => hlimit t t.property))
  have huniform : TendstoUniformlyOn H h atTop (Icc a b) :=
    tendstoUniformlyOn_iff_restrict.mpr hrestricted
  refine ⟨h, huniform.continuousOn (Eventually.of_forall hcont).frequently,
    hzero, huniform, ?_⟩
  intro eps heps
  obtain ⟨d, hd, hmod⟩ := hmodulus (eps / 2) (half_pos heps)
  refine ⟨d, hd, ?_⟩
  intro t ht htd
  have hb := le_of_tendsto' ((hlimit t ht).sub hstart).norm
    (fun j => (hmod j t ht htd).le)
  exact hb.trans_lt (half_lt_self heps)

end PoincareConjecture.M63
