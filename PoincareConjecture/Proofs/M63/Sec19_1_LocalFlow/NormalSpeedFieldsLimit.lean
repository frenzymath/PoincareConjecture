import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalizationLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceFirstJetCoefficientLimits
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedGradientLimit
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, ℝ)




theorem exists_normal_speed_fields_limits
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {K R J m0 V0 : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J)
    (hBounds : CurveEvolutionAmbientBounds F K K K) (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    (c : ℕ → ℝ → ℝ → M) (hc : ∀ j, M62ShrinkingCurve F (c j))
    (vinit : ℕ → ℝ) (v0 : ℝ) (hvinit : ∀ j, vinit j ∈ Icc m0 V0)
    (hv0 : Tendsto vinit atTop (𝓝 v0))
    (hinitial : ∀ j x, curveSpeed F (c j) a x = vinit j)
    (hcurv : ∀ j t, t ∈ Ioo a b → ∀ x, m62CurvatureSquared F (c j) t x ≤ R)
    (hjet : ∀ j t, t ∈ Ioo a b → ∀ x,
      (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F (c j) 1 t x) ≤
        J / Real.sqrt (t - a))
    (Rn Sn Hn : ℕ → C(Icc a b, X)) (r s h : C(Icc a b, X))
    (hRn : Tendsto Rn atTop (𝓝 r)) (hSn : Tendsto Sn atTop (𝓝 s))
    (hHn : Tendsto Hn atTop (𝓝 h))
    (hRrep : ∀ j (t : Icc a b) (x : ℝ), Rn j t (x : AddCircle curvePeriod) = e (c j x t))
    (hSrep : ∀ j (t : Icc a b) (x : ℝ), Sn j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (spatialUnitTangent F (c j) t x))
    (hHrep : ∀ j (t : Icc a b) (x : ℝ), Hn j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x))
    (hrU : ∀ (t : Icc a b) z, r t z ∈ U) :
    ∃ (Vn Wn : ℕ → ℝ → XR) (v g : ℝ → XR),
      (∀ j t, t ∈ Icc a b → ∀ x : ℝ,
        Vn j t (x : AddCircle curvePeriod) = curveSpeed F (c j) t x) ∧
      (∀ j t, t ∈ Icc a b → ∀ x : ℝ,
        Wn j t (x : AddCircle curvePeriod) = deriv (curveSpeed F (c j) t) x) ∧
      ContinuousOn v (Icc a b) ∧ ContinuousOn g (Icc a b) ∧
      TendstoUniformlyOn Vn v atTop (Icc a b) ∧
      TendstoUniformlyOn Wn g atTop (Icc a b) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ,
        m0 * Real.exp (-(K + R) * (b - a)) ≤ v t (x : AddCircle curvePeriod) ∧
        v t (x : AddCircle curvePeriod) ≤ V0 * Real.exp ((K + R) * (b - a))) ∧
      v a = ContinuousMap.const _ v0 ∧ g a = 0 ∧
      ∀ t ∈ Icc a b, ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => v t (y : AddCircle curvePeriod))
          (g t (x : AddCircle curvePeriod)) x := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  have hper (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      Function.Periodic (curveSpeed F (c j) t) curvePeriod :=
    speed_periodic F (c j) (hc j) ht
  have hderivper (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      Function.Periodic (deriv (curveSpeed F (c j) t)) curvePeriod := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun f : ℝ → ℝ => deriv f x) (funext (hper j t ht))
  let Vn : ℕ → ℝ → XR := fun j t => if ht : t ∈ Icc a b then
    ⟨(hper j t ht).lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
        (speed_contDiff F (c j) (hc j) ht).continuous⟩ else 0
  let Wn : ℕ → ℝ → XR := fun j t => if ht : t ∈ Icc a b then
    ⟨(hderivper j t ht).lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
        (speed_contDiff F (c j) (hc j) ht).continuous_deriv_one⟩ else 0
  have hVrep (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      Vn j t (x : AddCircle curvePeriod) = curveSpeed F (c j) t x := by
    simp only [Vn, dif_pos ht, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  have hWrep (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      Wn j t (x : AddCircle curvePeriod) = deriv (curveSpeed F (c j) t) x := by
    simp only [Wn, dif_pos ht, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  obtain ⟨Ac, A0c, hAc, hArep, _hA0rep⟩ :=
    exists_closed_normalization_coefficient_limit F he hU heU hρ hρe c
      Rn Sn Hn r s h hRn hSn hHn hRrep hSrep hHrep hrU
  let A : ℕ → ℝ → XR := fun j t => if ht : t ∈ Icc a b then Ac j ⟨t, ht⟩ else 0
  let A0 : ℝ → XR := fun t => if ht : t ∈ Icc a b then A0c ⟨t, ht⟩ else 0
  have hAactual (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      A j t (x : AddCircle curvePeriod) =
        m62TangentRicci F (c j) t x + m62CurvatureSquared F (c j) t x := by
    simpa only [A, dif_pos (Ioo_subset_Icc_self ht)] using
      hArep j ⟨t, Ioo_subset_Icc_self ht⟩ x
  have hAlim (t : ℝ) (ht : t ∈ Ioo a b) :
      Tendsto (fun j => A j t) atTop (𝓝 (A0 t)) := by
    simpa +instances only [A, A0, dif_pos (Ioo_subset_Icc_self ht), Function.comp_def] using!
      (continuous_eval_const (⟨t, Ioo_subset_Icc_self ht⟩ : Icc a b)).tendsto A0c |>.comp hAc
  obtain ⟨v, hvc, hVlim, _hvformula, hvbounds, hvstart⟩ :=
    exists_uniform_normalSpeed_limit F hab hK hR hBounds hm0 hmV c hc
      vinit v0 hvinit hv0 hinitial hcurv Vn A A0 hVrep hAactual hAlim
  have hBexists (t : ℝ) (ht : t ∈ Ioo a b) :
      ∃ (B : ℕ → XR) (b0 : XR),
        (∀ j (x : ℝ), B j (x : AddCircle curvePeriod) =
          deriv (fun y => m62TangentRicci F (c j) t y + m62CurvatureSquared F (c j) t y) x) ∧
        Tendsto B atTop (𝓝 b0) := by
    let t0 : Icc a b := ⟨t, Ioo_subset_Icc_self ht⟩
    obtain ⟨_Dn, _J1n, B, _dh, _j1, b0, _hDrep, _hJrep, hBrep,
        _hDlim, _hJlim, hBlim, _hrest⟩ :=
      exists_normalFirstJet_normalizationDerivative_limits F hcompact he hU heU hρ hρe
        c hc hR hm0 hmV vinit hvinit hinitial hcurv ht
        (fun j => Rn j t0) (fun j => Sn j t0) (fun j => Hn j t0) (fun j => Vn j t)
        (r t0) (s t0) (h t0) (v t)
        ((continuous_eval_const t0).tendsto r |>.comp hRn)
        ((continuous_eval_const t0).tendsto s |>.comp hSn)
        ((continuous_eval_const t0).tendsto h |>.comp hHn)
        (hVlim.tendsto_at (Ioo_subset_Icc_self ht))
        (fun j => hRrep j t0) (fun j => hSrep j t0) (fun j => hHrep j t0)
        (fun j => hVrep j t (Ioo_subset_Icc_self ht)) (hrU t0)
    exact ⟨B, b0, hBrep, hBlim⟩
  choose Bsub bsub hBsubrep hBsublim using fun t : Ioo a b => hBexists t t.property
  let B : ℕ → ℝ → XR := fun j t => if ht : t ∈ Ioo a b then Bsub ⟨t, ht⟩ j else 0
  let B0 : ℝ → XR := fun t => if ht : t ∈ Ioo a b then bsub ⟨t, ht⟩ else 0
  have hBactual (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      B j t (x : AddCircle curvePeriod) =
        deriv (fun y => m62TangentRicci F (c j) t y + m62CurvatureSquared F (c j) t y) x := by
    simpa only [B, dif_pos ht] using hBsubrep ⟨t, ht⟩ j x
  have hBlim (t : ℝ) (ht : t ∈ Ioo a b) :
      Tendsto (fun j => B j t) atTop (𝓝 (B0 t)) := by
    simpa only [B, B0, dif_pos ht] using hBsublim ⟨t, ht⟩
  obtain ⟨g, hgc, hWlim, _hgformula, hgstart, hderiv⟩ :=
    exists_uniform_normalSpeedGradient_limit F hab hK hR hJ hBounds hm0 hmV
      c hc vinit hvinit hinitial hcurv hjet Vn Wn B v B0
      hVrep hWrep hBactual hvc hVlim hBlim
  exact ⟨Vn, Wn, v, g, hVrep, hWrep, hvc, hgc, hVlim, hWlim,
    hvbounds, hvstart, hgstart, hderiv⟩

end PoincareConjecture.M63
