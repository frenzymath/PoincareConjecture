import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedGradient
import PoincareConjecture.Proofs.M63.Mathlib.DominatedPrimitiveConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {a b : ℝ}

local notation "X" => C(AddCircle curvePeriod, ℝ)

theorem exists_uniform_normalSpeedGradient_limit
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    {K R J m0 V0 : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    (c : ℕ → ℝ → ℝ → M) (hc : ∀ j, M62ShrinkingCurve F (c j))
    (v0n : ℕ → ℝ) (hv0n : ∀ j, v0n j ∈ Icc m0 V0)
    (hinitial : ∀ j x, curveSpeed F (c j) a x = v0n j)
    (hcurv : ∀ j t, t ∈ Ioo a b → ∀ x, m62CurvatureSquared F (c j) t x ≤ R)
    (hjet : ∀ j t, t ∈ Ioo a b → ∀ x,
      (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F (c j) 1 t x) ≤
        J / Real.sqrt (t - a))
    (V W B : ℕ → ℝ → X) (v B0 : ℝ → X)
    (hVrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ,
      V j t (x : AddCircle curvePeriod) = curveSpeed F (c j) t x)
    (hWrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ,
      W j t (x : AddCircle curvePeriod) = deriv (curveSpeed F (c j) t) x)
    (hBrep : ∀ j t, t ∈ Ioo a b → ∀ x : ℝ,
      B j t (x : AddCircle curvePeriod) =
        deriv (fun y => m62TangentRicci F (c j) t y + m62CurvatureSquared F (c j) t y) x)
    (hvc : ContinuousOn v (Icc a b))
    (hVlim : TendstoUniformlyOn V v atTop (Icc a b))
    (hBlim : ∀ t ∈ Ioo a b, Tendsto (fun j => B j t) atTop (𝓝 (B0 t))) :
    let _ : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
    ∃ g : ℝ → X, ContinuousOn g (Icc a b) ∧
      TendstoUniformlyOn W g atTop (Icc a b) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ, g t (x : AddCircle curvePeriod) =
        -v t (x : AddCircle curvePeriod) *
          ((∫ r in a..t, B0 r) (x : AddCircle curvePeriod))) ∧
      g a = 0 ∧
      ∀ t ∈ Icc a b, ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => v t (y : AddCircle curvePeriod))
          (g t (x : AddCircle curvePeriod)) x := by
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  let Vcap := V0 * Real.exp ((K + R) * (b - a))
  have hVcap0 : 0 ≤ Vcap := mul_nonneg (hm0.le.trans hmV) (Real.exp_pos _).le
  have hVcap (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      curveSpeed F (c j) t x ≤ Vcap := by
    have h := (curveSpeed_exp_bounds F (c j) (hc j) hBounds x
      (fun r hr => hcurv j r hr x) ha ht ht.1).2
    rw [hinitial j x] at h
    exact h.trans (mul_le_mul (hv0n j).2
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (sub_le_sub_right ht.2 a) (add_nonneg hK hR)))
      (Real.exp_pos _).le (hm0.le.trans hmV))
  let major : ℝ → ℝ := fun t => Vcap * (K + 2 * K * Real.sqrt R) +
    (2 * Vcap * Real.sqrt R * J) * (t - a) ^ (-(1 / 2 : ℝ))
  have hmajor (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) : ‖B j t‖ ≤ major t := by
    have hage : 0 ≤ t - a := sub_nonneg.mpr ht.1.le
    have hmajor0 : 0 ≤ major t := by dsimp only [major]; positivity
    apply (ContinuousMap.norm_le (B j t) hmajor0).mpr
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hBrep j t ht x, Real.norm_eq_abs]
    have hk0 := curvature_nonneg F (c j) t x
    have hk : m62Curvature F (c j) t x ≤ Real.sqrt R := by
      nlinarith only [curvature_nonneg F (c j) t x, curvature_sq F (c j) t x,
        hcurv j t ht x, Real.sq_sqrt hR, Real.sqrt_nonneg R]
    have hu : 0 ≤ J / Real.sqrt (t - a) := div_nonneg hJ (Real.sqrt_nonneg _)
    have hco : K + 2 * K * m62Curvature F (c j) t x +
        2 * m62Curvature F (c j) t x *
          (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F (c j) 1 t x) ≤
        K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (t - a)) := by
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hk (by positivity))
      · exact (mul_le_mul_of_nonneg_left (hjet j t ht x)
          (by positivity)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hu)
    have hp : (t - a) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (t - a))⁻¹ := by
      rw [Real.rpow_neg (sub_nonneg.mpr ht.1.le), ← Real.sqrt_eq_rpow]
    calc
      _ ≤ curveSpeed F (c j) t x *
          (K + 2 * K * m62Curvature F (c j) t x +
            2 * m62Curvature F (c j) t x *
              (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F (c j) 1 t x)) :=
        normalizationCoefficient_spatial_abs_bound F (c j) (hc j) hBounds ht x
      _ ≤ curveSpeed F (c j) t x *
          (K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (t - a))) :=
        mul_le_mul_of_nonneg_left hco (speed_nonneg F (c j) t x)
      _ ≤ Vcap * (K + 2 * K * Real.sqrt R +
          2 * Real.sqrt R * (J / Real.sqrt (t - a))) :=
        mul_le_mul_of_nonneg_right (hVcap j t (Ioo_subset_Icc_self ht) x) (by positivity)
      _ = major t := by dsimp only [major]; rw [hp]; ring
  have hpow : IntervalIntegrable (fun t : ℝ => (t - a) ^ (-(1 / 2 : ℝ))) volume a b := by
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b - a)
        (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_right a
  have hmajori : IntegrableOn major (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp
      (intervalIntegrable_const.add (hpow.const_mul _))
  let N : ℕ → ℝ × ℝ → ℝ := fun j z =>
    m62TangentRicci F (c j) z.2 z.1 + m62CurvatureSquared F (c j) z.2 z.1
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hN (j : ℕ) : ContDiffOn ℝ ∞ (N j) (univ ×ˢ Ioo a b) :=
    normalization_coefficient_contDiffOn F (c j) (hc j)
  have hDN (j : ℕ) : ContDiffOn ℝ ∞ (M08.coordinatePartialS (N j))
      (univ ×ˢ Ioo a b) := M08.coordinatePartialS_contDiffOn hopen (N j) (hN j)
  have hder (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun y => N j (y, t)) (M08.coordinatePartialS (N j) (x, t)) x := by
    have hd : DifferentiableAt ℝ (N j) (x, t) :=
      ((hN j).contDiffAt (hopen.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt (by simp)
    exact M08.coordinateSlice_fst_hasDerivAt (N j) (p := (x, t)) hd
  have hBc (j : ℕ) : ContinuousOn (B j) (Ioo a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : Ioo a b × ℝ => (p.1, (p.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    have hcomp : Continuous (fun p : Ioo a b × ℝ =>
        M08.coordinatePartialS (N j) (p.2, p.1.1)) :=
      (hDN j).continuousOn.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨mem_univ _, p.1.2⟩)
    exact hcomp.congr (fun p =>
      ((hBrep j p.1.1 p.1.2 p.2).trans (hder j p.1.1 p.1.2 p.2).deriv).symm)
  obtain ⟨hBi, _hB0i, hIc, hIlim⟩ :=
    intervalIntegral.tendstoUniformlyOn_primitive_of_dominated
      (fn := B) (f := B0) (μ := volume) (bound := major) hab.le
      (fun j => by
        rw [← restrict_Ioo_eq_restrict_Icc]
        exact (hBc j).aestronglyMeasurable measurableSet_Ioo) hmajori
      (fun j => by
        rw [← restrict_Ioo_eq_restrict_Icc]
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact hmajor j t ht)
      (by
        rw [← restrict_Ioo_eq_restrict_Icc]
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact hBlim t ht)
  let I : ℝ → X := fun t => ∫ r in a..t, B0 r
  let In : ℕ → ℝ → X := fun j t => ∫ r in a..t, B j r
  let g : ℝ → X := fun t => -v t * I t
  let gn : ℕ → ℝ → X := fun j t => -V j t * In j t
  have hInc (j : ℕ) : ContinuousOn (In j) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' (a := a) (hBi j) (by
        simpa only [uIcc_of_le hab.le] using ha)
  have hVc (j : ℕ) : ContinuousOn (V j) (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : Icc a b × ℝ => (p.1, (p.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    have hcomp : Continuous (fun p : Icc a b × ℝ => curveSpeed F (c j) p.1.1 p.2) :=
      (speed_continuousOn F (c j) (hc j)).comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨mem_univ _, p.1.2⟩)
    exact hcomp.congr (fun p => (hVrep j p.1.1 p.1.2 p.2).symm)
  have hgc : ContinuousOn g (Icc a b) := hvc.neg.mul hIc
  have hgnc (j : ℕ) : ContinuousOn (gn j) (Icc a b) := (hVc j).neg.mul (hInc j)
  have hgnlim : TendstoUniformlyOn gn g atTop (Icc a b) := by
    have hVp := (hvc.tendsto_domRestrict_iff_tendstoUniformlyOn hVc).mpr hVlim
    have hIp := (hIc.tendsto_domRestrict_iff_tendstoUniformlyOn hInc).mpr hIlim
    apply (hgc.tendsto_domRestrict_iff_tendstoUniformlyOn hgnc).mp
    exact hVp.neg.mul hIp
  have heq (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : W j t = gn j t := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change W j t (x : AddCircle curvePeriod) =
      -V j t (x : AddCircle curvePeriod) *
        ((∫ r in a..t, B j r) (x : AddCircle curvePeriod))
    rw [hWrep j t ht x, hVrep j t ht x]
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl ht.2
    have hEval : (∫ r in a..t, B j r) (x : AddCircle curvePeriod) =
        ∫ r in a..t,
          deriv (fun y => m62TangentRicci F (c j) r y + m62CurvatureSquared F (c j) r y) x := by
      have hcomm : (∫ r in a..t, B j r) (x : AddCircle curvePeriod) =
          ∫ r in a..t, B j r (x : AddCircle curvePeriod) :=
        ((ContinuousMap.evalCLM ℝ (x : AddCircle curvePeriod)).intervalIntegral_comp_comm
          ((hBi j).mono_set hsub)).symm
      rw [hcomm]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne t] with r hrt
      intro hr
      rw [uIoc_of_le ht.1] at hr
      exact hBrep j r ⟨hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le ht.2⟩ x
    rw [hEval]
    exact curveSpeed_spatial_derivative_integral F (c j) (hc j) hK hR hJ
      (hm0.trans_le (hv0n j).1) hBounds (hinitial j) (hcurv j) (hjet j) ht x
  have hWlim : TendstoUniformlyOn W g atTop (Icc a b) :=
    hgnlim.congr (Eventually.of_forall fun j t ht => (heq j t ht).symm)
  refine ⟨g, hgc, hWlim, fun _ _ _ => rfl, ?_, ?_⟩
  · change -v a * (∫ r in a..a, B0 r) = 0
    rw [intervalIntegral.integral_same, mul_zero]
  · intro t ht x
    have hWu := (ContinuousMap.tendsto_iff_tendstoUniformly.mp
      (hWlim.tendsto_at ht)).comp (fun y : ℝ => (y : AddCircle curvePeriod))
    apply hasDerivAt_of_tendstoUniformly
      (f := fun j (y : ℝ) => V j t (y : AddCircle curvePeriod)) hWu
      (Eventually.of_forall ?_) ?_ x
    · intro j y
      have hfun : (fun z : ℝ => V j t (z : AddCircle curvePeriod)) =
          curveSpeed F (c j) t := funext (hVrep j t ht)
      change HasDerivAt (fun z : ℝ => V j t (z : AddCircle curvePeriod))
        (W j t (y : AddCircle curvePeriod)) y
      rw [hfun, hWrep j t ht y]
      exact ((speed_contDiff F (c j) (hc j) ht).differentiable (by norm_num) y).hasDerivAt
    · intro y
      exact (continuous_eval_const (y : AddCircle curvePeriod)).tendsto (v t)
        |>.comp (hVlim.tendsto_at ht)

end PoincareConjecture.M63
