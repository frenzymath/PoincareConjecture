import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalizationLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedLimit
import Mathlib.Topology.Order.ProjIcc










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, ℝ)




theorem normalField_c2_reconstruction_with_anchored_speed
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U)
    {ρ : W → M} (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    (hρe : ∀ p, ρ (e p) = p)
    {K R m0 V0 : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    (cn : ℕ → ℝ → ℝ → M) (hcn : ∀ j, M62ShrinkingCurve F (cn j))
    (vinit : ℕ → ℝ) (v0 : ℝ) (hvinit : ∀ j, vinit j ∈ Icc m0 V0)
    (hv0 : Tendsto vinit atTop (𝓝 v0))
    (hinitial : ∀ j x, curveSpeed F (cn j) a x = vinit j)
    (hcurv : ∀ j t, t ∈ Ioo a b → ∀ x, m62CurvatureSquared F (cn j) t x ≤ R)
    (Rn Sn Hn : ℕ → C(Icc a b, X)) (r s h : C(Icc a b, X))
    (hRn : Tendsto Rn atTop (𝓝 r)) (hSn : Tendsto Sn atTop (𝓝 s))
    (hHn : Tendsto Hn atTop (𝓝 h))
    (hRrep : ∀ j (t : Icc a b) (x : ℝ),
      Rn j t (x : AddCircle curvePeriod) = e (cn j x t))
    (hSrep : ∀ j (t : Icc a b) (x : ℝ), Sn j t (x : AddCircle curvePeriod) =
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (cn j x t) (spatialUnitTangent F (cn j) t x) : W))
    (hHrep : ∀ j (t : Icc a b) (x : ℝ), Hn j t (x : AddCircle curvePeriod) =
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (cn j x t) (m62CurvatureVector F (cn j) t x) : W))
    (hrU : ∀ (t : Icc a b) z, r t z ∈ U)
    (Vn Wn : ℕ → ℝ → XR) (v g : ℝ → XR)
    (hVrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ,
      Vn j t (x : AddCircle curvePeriod) = curveSpeed F (cn j) t x)
    (hWrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ,
      Wn j t (x : AddCircle curvePeriod) = deriv (curveSpeed F (cn j) t) x)
    (hv : ContinuousOn v (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hV : TendstoUniformlyOn Vn v atTop (Icc a b))
    (hW : TendstoUniformlyOn Wn g atTop (Icc a b))
    (hvpos : ∀ t ∈ Icc a b, ∀ x : ℝ, 0 < v t (x : AddCircle curvePeriod)) :
    let c : ℝ → ℝ → M := fun x t =>
      ρ (r (projIcc a b hab.le t) (x : AddCircle curvePeriod))
    M63C2ShrinkingCurveOn F c (Icc a b) ∧
      (∀ (t : Icc a b) (x : ℝ), e (c x t) = r t (x : AddCircle curvePeriod) ∧
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x) : W) =
          s t (x : AddCircle curvePeriod) ∧
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) : W) =
          h t (x : AddCircle curvePeriod) ∧
        curveSpeed F c t x = v t (x : AddCircle curvePeriod) ∧
        deriv (curveSpeed F c t) x = g t (x : AddCircle curvePeriod)) ∧
      (∀ x, curveSpeed F c a x = v0) ∧
      ∀ tau t, a ≤ tau → tau ≤ t → t ≤ b → ∀ x,
        curveSpeed F c t x = curveSpeed F c tau x * Real.exp
          (-∫ u in tau..t, m62TangentRicci F c u x + m62CurvatureSquared F c u x) := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  let pi : ℝ → Icc a b := projIcc a b hab.le
  let c : ℝ → ℝ → M := fun x t => ρ (r (pi t) (x : AddCircle curvePeriod))
  have hpi : Continuous pi := continuous_projIcc
  have hpi_val (t : ℝ) (ht : t ∈ Icc a b) : pi t = ⟨t, ht⟩ :=
    projIcc_of_mem hab.le ht
  have hlim (Qn : ℕ → C(Icc a b, X)) (q : C(Icc a b, X))
      (hQ : Tendsto Qn atTop (𝓝 q)) :
      TendstoUniformlyOn (fun j t => Qn j (pi t)) (fun t => q (pi t)) atTop (Icc a b) :=
    ((ContinuousMap.tendsto_iff_tendstoUniformly.mp hQ).comp pi).tendstoUniformlyOn
  obtain ⟨hc, hfields, _htime, _htrace⟩ :=
    normalCurve_c2_of_uniform_embedded_field_limits F he hU heU hρ hρe cn hcn
      (fun j t => Rn j (pi t)) (fun j t => Sn j (pi t)) (fun j t => Hn j (pi t))
      Vn Wn
      (fun j t ht x => by simpa only [hpi_val t ht] using hRrep j ⟨t, ht⟩ x)
      (fun j t ht x => by simpa only [hpi_val t ht] using hSrep j ⟨t, ht⟩ x)
      (fun j t ht x => by simpa only [hpi_val t ht] using hHrep j ⟨t, ht⟩ x)
      hVrep hWrep (fun t => r (pi t)) (fun t => s (pi t)) (fun t => h (pi t)) v g
      (r.continuous.comp hpi).continuousOn (s.continuous.comp hpi).continuousOn
      (h.continuous.comp hpi).continuousOn hv hg
      (hlim Rn r hRn) (hlim Sn s hSn) (hlim Hn h hHn) hV hW
      (fun t _ x => hrU (pi t) (x : AddCircle curvePeriod)) hvpos
  have hspeed (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      curveSpeed F c t x = v t (x : AddCircle curvePeriod) :=
    (hfields t ht x).2.2.1
  have hgrad (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      deriv (curveSpeed F c t) x = g t (x : AddCircle curvePeriod) :=
    (hfields t ht x).2.2.2.1
  have hHactual (t : Icc a b) (x : ℝ) :
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) : W) =
        h t (x : AddCircle curvePeriod) := by
    simpa only [hpi_val t t.property] using (hfields t t.property x).2.2.2.2
  have hrfix (t : Icc a b) (x : ℝ) : e (c x t) = r t (x : AddCircle curvePeriod) := by
    have hz := (continuous_eval_const (x : AddCircle curvePeriod)).tendsto (r t)
      |>.comp ((continuous_eval_const t).tendsto r |>.comp hRn)
    have hguard (j : ℕ) : Rn j t (x : AddCircle curvePeriod) ∈ U := by
      rw [hRrep]
      exact heU (mem_range_self _)
    have hpost := ((he.continuous.comp_continuousOn hρ.continuousOn)
      _ (hrU t (x : AddCircle curvePeriod))).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hz, Eventually.of_forall hguard⟩)
    have heq (j : ℕ) : e (ρ (Rn j t (x : AddCircle curvePeriod))) =
        Rn j t (x : AddCircle curvePeriod) := by rw [hRrep, hρe]
    have hfixed := tendsto_nhds_unique
      (hpost.congr' (Eventually.of_forall heq)) hz
    simpa only [c, hpi_val t t.property, Function.comp_def] using hfixed
  have hdata := c2ShrinkingCurve_embedded_closed_data hc he
  have hSactual (t : Icc a b) (x : ℝ) :
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x) : W) =
        s t (x : AddCircle curvePeriod) := by
    have hfirst : HasDerivAt (fun y : ℝ => r t (y : AddCircle curvePeriod))
        (v t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod)) x := by
      simpa only [hpi_val t t.property] using (hfields t t.property x).1
    have hpush : (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
        (curveVelocity (fun y => c y t) x) : W) =
        v t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod) :=
      ((hdata.2.1 t t.property x).congr_of_eventuallyEq
        (Eventually.of_forall (fun y => (hrfix t y).symm))).unique hfirst
    rw [spatialUnitTangent, map_smul, hpush, hspeed t t.property x,
      smul_smul, inv_mul_cancel₀ (hvpos t t.property x).ne', one_smul]
  obtain ⟨Ac, A0c, hAc, hArep, hA0rep⟩ :=
    exists_closed_normalization_coefficient_limit F he hU heU hρ hρe cn
      Rn Sn Hn r s h hRn hSn hHn hRrep hSrep hHrep hrU
  let A : ℕ → ℝ → XR := fun j t => Ac j (pi t)
  let A0 : ℝ → XR := fun t => A0c (pi t)
  have hA0c : Continuous A0 := A0c.continuous.comp hpi
  have hAactual (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      A j t (x : AddCircle curvePeriod) =
        m62TangentRicci F (cn j) t x + m62CurvatureSquared F (cn j) t x := by
    simpa only [A, hpi_val t (Ioo_subset_Icc_self ht)] using
      hArep j ⟨t, Ioo_subset_Icc_self ht⟩ x
  have hAlim (t : ℝ) (_ht : t ∈ Ioo a b) :
      Tendsto (fun j => A j t) atTop (𝓝 (A0 t)) :=
    (continuous_eval_const (pi t)).tendsto A0c |>.comp hAc
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hA0actual (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      A0 t (x : AddCircle curvePeriod) =
        m62TangentRicci F c t x + m62CurvatureSquared F c t x := by
    simp only [A0, hpi_val t ht]
    rw [hA0rep, ← hSactual ⟨t, ht⟩ x, ← hHactual ⟨t, ht⟩ x, ← hrfix ⟨t, ht⟩ x,
      hleft, hleft, hρe]
    rfl
  obtain ⟨v', _hv'cont, hV', hformula, _hv'bounds, _hv'initial⟩ :=
    exists_uniform_normalSpeed_limit F hab hK hR hBounds hm0 hmV cn hcn
      vinit v0 hvinit hv0 hinitial hcurv Vn A A0 hVrep hAactual hAlim
  have heq (t : ℝ) (ht : t ∈ Icc a b) : v' t = v t :=
    tendsto_nhds_unique (hV'.tendsto_at ht) (hV.tendsto_at ht)
  have hscalar (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      v t (x : AddCircle curvePeriod) =
        v0 * Real.exp (-∫ u in a..t, A0 u (x : AddCircle curvePeriod)) := by
    rw [← heq t ht, hformula t ht x]
    have hcomm : (∫ u in a..t, A0 u) (x : AddCircle curvePeriod) =
        ∫ u in a..t, A0 u (x : AddCircle curvePeriod) :=
      ((ContinuousMap.evalCLM ℝ (x : AddCircle curvePeriod)).intervalIntegral_comp_comm
        (hA0c.intervalIntegrable a t)).symm
    rw [hcomm]
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro t x
    exact ⟨hrfix t x, hSactual t x, hHactual t x,
      hspeed t t.property x, hgrad t t.property x⟩
  · intro x
    rw [hspeed a ⟨le_rfl, hab.le⟩ x, hscalar a ⟨le_rfl, hab.le⟩ x,
      intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one]
  · intro tau t hatau htaut htb x
    have ht : t ∈ Icc a b := ⟨hatau.trans htaut, htb⟩
    have htau : tau ∈ Icc a b := ⟨hatau, htaut.trans htb⟩
    have hcx : Continuous (fun u => A0 u (x : AddCircle curvePeriod)) :=
      (continuous_eval_const (x : AddCircle curvePeriod)).comp hA0c
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hcx.intervalIntegrable a tau) (hcx.intervalIntegrable tau t)
    have hInt : (∫ u in tau..t, A0 u (x : AddCircle curvePeriod)) =
        ∫ u in tau..t, m62TangentRicci F c u x + m62CurvatureSquared F c u x := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le htaut] at hu
      exact hA0actual u ⟨hatau.trans hu.1, hu.2.trans htb⟩ x
    rw [hspeed t ht x, hspeed tau htau x, hscalar t ht x, hscalar tau htau x,
      ← hInt, ← hsplit, neg_add, Real.exp_add, mul_assoc]

end PoincareConjecture.M63
