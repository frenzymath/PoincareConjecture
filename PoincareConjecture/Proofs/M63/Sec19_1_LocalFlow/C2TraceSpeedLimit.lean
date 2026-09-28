import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeed
import PoincareConjecture.Proofs.M63.Mathlib.DominatedPrimitiveConvergence
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
  {a b : ℝ}

local notation "X" => C(AddCircle curvePeriod, ℝ)





theorem exists_uniform_normalSpeed_limit
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    {K R m0 V0 : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hBounds : CurveEvolutionAmbientBounds F K K K) (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    (c : ℕ → ℝ → ℝ → M) (hc : ∀ j, M62ShrinkingCurve F (c j))
    (v0n : ℕ → ℝ) (v0 : ℝ) (hv0n : ∀ j, v0n j ∈ Icc m0 V0)
    (hv0 : Tendsto v0n atTop (𝓝 v0))
    (hinitial : ∀ j x, curveSpeed F (c j) a x = v0n j)
    (hcurv : ∀ j t, t ∈ Ioo a b → ∀ x, m62CurvatureSquared F (c j) t x ≤ R)
    (V A : ℕ → ℝ → X) (A0 : ℝ → X)
    (hVrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ,
      V j t (x : AddCircle curvePeriod) = curveSpeed F (c j) t x)
    (hArep : ∀ j t, t ∈ Ioo a b → ∀ x : ℝ,
      A j t (x : AddCircle curvePeriod) =
        m62TangentRicci F (c j) t x + m62CurvatureSquared F (c j) t x)
    (hAlim : ∀ t ∈ Ioo a b, Tendsto (fun j => A j t) atTop (𝓝 (A0 t))) :
    let _ : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
    ∃ v : ℝ → X, ContinuousOn v (Icc a b) ∧
      TendstoUniformlyOn V v atTop (Icc a b) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ, v t (x : AddCircle curvePeriod) =
        v0 * Real.exp (-((∫ r in a..t, A0 r) (x : AddCircle curvePeriod)))) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ,
        m0 * Real.exp (-(K + R) * (b - a)) ≤ v t (x : AddCircle curvePeriod) ∧
        v t (x : AddCircle curvePeriod) ≤ V0 * Real.exp ((K + R) * (b - a))) ∧
      v a = ContinuousMap.const _ v0 := by
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hAc (j : ℕ) : ContinuousOn (A j) (Ioo a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : Ioo a b × ℝ => (p.1, (p.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    have hcont := (normalization_coefficient_contDiffOn F (c j) (hc j)).continuousOn
    have hcomp : Continuous (fun p : Ioo a b × ℝ =>
        m62TangentRicci F (c j) p.1.1 p.2 + m62CurvatureSquared F (c j) p.1.1 p.2) :=
      hcont.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨mem_univ _, p.1.2⟩)
    exact hcomp.congr (fun p => (hArep j p.1.1 p.1.2 p.2).symm)
  have hAb (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) : ‖A j t‖ ≤ K + R := by
    apply (ContinuousMap.norm_le (A j t) (add_nonneg hK hR)).mpr
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hArep j t ht x, Real.norm_eq_abs]
    have hu := (unitTangent_norm F (c j) (hc j) (Ioo_subset_Icc_self ht) x).le
    have hRic : |m62TangentRicci F (c j) t x| ≤ K :=
      hBounds.ricci t (Ioo_subset_Icc_self ht) (c j x t)
        (spatialUnitTangent F (c j) t x) (spatialUnitTangent F (c j) t x) hu hu
    calc
      _ ≤ |m62TangentRicci F (c j) t x| + |m62CurvatureSquared F (c j) t x| :=
        abs_add_le _ _
      _ = |m62TangentRicci F (c j) t x| + m62CurvatureSquared F (c j) t x := by
        rw [abs_of_nonneg (curvatureSquared_nonneg F (c j) t x)]
      _ ≤ K + R := add_le_add hRic (hcurv j t ht x)
  obtain ⟨hAi, _hA0i, hIc, hIlim⟩ :=
    intervalIntegral.tendstoUniformlyOn_primitive_of_dominated
      (fn := A) (f := A0) (μ := volume) (bound := fun _ => K + R) hab.le
      (fun j => by
        rw [← restrict_Ioo_eq_restrict_Icc]
        exact (hAc j).aestronglyMeasurable measurableSet_Ioo)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp intervalIntegrable_const)
      (fun j => by
        rw [← restrict_Ioo_eq_restrict_Icc]
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact hAb j t ht)
      (by
        rw [← restrict_Ioo_eq_restrict_Icc]
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
        exact hAlim t ht)
  let I : ℝ → X := fun t => ∫ r in a..t, A0 r
  let In : ℕ → ℝ → X := fun j t => ∫ r in a..t, A j r
  let ex : C(ℝ, ℝ) := ⟨Real.exp, Real.continuous_exp⟩
  let Ex : C(X, X) := ⟨fun w => ex.comp (-w), ex.continuous_postcomp.comp continuous_neg⟩
  let v : ℝ → X := fun t => v0 • Ex (I t)
  let vn : ℕ → ℝ → X := fun j t => v0n j • Ex (In j t)
  have hInc (j : ℕ) : ContinuousOn (In j) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' (a := a) (hAi j) (by
        simpa only [uIcc_of_le hab.le] using ha)
  have hvc : ContinuousOn v (Icc a b) := by
    simpa +instances only [v, I, Function.comp_def, Pi.smul_apply] using!
      (continuousOn_const (c := v0)).smul (Ex.continuous.comp_continuousOn hIc)
  have hvnc (j : ℕ) : ContinuousOn (vn j) (Icc a b) := by
    simpa +instances only [vn, Function.comp_def, Pi.smul_apply] using!
      (continuousOn_const (c := v0n j)).smul (Ex.continuous.comp_continuousOn (hInc j))
  have hvnlim : TendstoUniformlyOn vn v atTop (Icc a b) := by
    let P : C(Icc a b, X) := ⟨_, hIc.domRestrict⟩
    let Pn : ℕ → C(Icc a b, X) := fun j => ⟨_, (hInc j).domRestrict⟩
    have hP : Tendsto Pn atTop (𝓝 P) :=
      (hIc.tendsto_domRestrict_iff_tendstoUniformlyOn hInc).mpr hIlim
    have hE := (Ex.continuous_postcomp.tendsto P).comp hP
    have hmul := hv0.smul hE
    apply (hvc.tendsto_domRestrict_iff_tendstoUniformlyOn hvnc).mp
    exact hmul
  have heq (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : V j t = vn j t := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hVrep j t ht x]
    change curveSpeed F (c j) t x =
      v0n j * Real.exp (-((∫ r in a..t, A j r) (x : AddCircle curvePeriod)))
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl ht.2
    have hEval : (∫ r in a..t, A j r) (x : AddCircle curvePeriod) =
        ∫ r in a..t, m62TangentRicci F (c j) r x + m62CurvatureSquared F (c j) r x := by
      have hcomm : (∫ r in a..t, A j r) (x : AddCircle curvePeriod) =
          ∫ r in a..t, A j r (x : AddCircle curvePeriod) :=
        ((ContinuousMap.evalCLM ℝ (x : AddCircle curvePeriod)).intervalIntegral_comp_comm
          ((hAi j).mono_set hsub)).symm
      rw [hcomm]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne t] with r hrt
      intro hr
      rw [uIoc_of_le ht.1] at hr
      exact hArep j r ⟨hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le ht.2⟩ x
    rw [hEval]
    calc
      _ = Real.exp (Real.log (curveSpeed F (c j) t x)) :=
        (Real.exp_log (speed_pos F (c j) (hc j) ht x)).symm
      _ = _ := by
        rw [curveSpeed_log_eq_integral F (c j) (hc j) hBounds x
          (fun r hr => hcurv j r hr x) ha ht ht.1, hinitial j x,
          sub_eq_add_neg, Real.exp_add, Real.exp_log (hm0.trans_le (hv0n j).1)]
  have hVlim : TendstoUniformlyOn V v atTop (Icc a b) :=
    hvnlim.congr (Eventually.of_forall fun j t ht => (heq j t ht).symm)
  refine ⟨v, hvc, hVlim, fun _ _ _ => rfl, ?_, ?_⟩
  · intro t ht x
    have hvl := (continuous_eval_const (x : AddCircle curvePeriod)).tendsto (v t)
      |>.comp (hVlim.tendsto_at ht)
    have hbound (j : ℕ) :
        m0 * Real.exp (-(K + R) * (b - a)) ≤ V j t (x : AddCircle curvePeriod) ∧
        V j t (x : AddCircle curvePeriod) ≤ V0 * Real.exp ((K + R) * (b - a)) := by
      rw [hVrep j t ht x]
      have h := curveSpeed_exp_bounds F (c j) (hc j) hBounds x
        (fun r hr => hcurv j r hr x) ha ht ht.1
      rw [hinitial j x] at h
      constructor
      · refine (mul_le_mul (hv0n j).1 ?_ (Real.exp_pos _).le
          (hm0.trans_le (hv0n j).1).le).trans h.1
        apply Real.exp_le_exp.mpr
        nlinarith only [ht.2, add_nonneg hK hR]
      · refine h.2.trans (mul_le_mul (hv0n j).2 ?_ (Real.exp_pos _).le (hm0.le.trans hmV))
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (add_nonneg hK hR))
    exact ⟨ge_of_tendsto hvl (Eventually.of_forall fun j => (hbound j).1),
      le_of_tendsto hvl (Eventually.of_forall fun j => (hbound j).2)⟩
  · apply ContinuousMap.ext
    intro z
    change v0 * Real.exp (-((∫ r in a..a, A0 r) z)) = v0
    simp only [intervalIntegral.integral_same, ContinuousMap.zero_apply, neg_zero,
      Real.exp_zero, mul_one]

end PoincareConjecture.M63
