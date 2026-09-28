import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.BallHitting
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.PositiveRetraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelMap
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurvePasting
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Junction









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology Bundle
namespace PoincareConjecture.LeviCivitaData
private theorem short_geodesic
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    (p : M) {r : ℝ} (hr : 0 < r) (x y : M)
    (hx : x ∈ g.ball p r) (hy : y ∈ g.ball p r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = x ∧ γ 1 = y ∧
      (g.edist x y).toReal ≤ 2 * r ∧ g.edist x y ≠ ⊤ ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        g.edist p (γ s) ≤ ENNReal.ofReal (3 * r) ∧
        g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) =
          (g.edist x y).toReal := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hxy : g.edist x y ≤ ENNReal.ofReal (2*r) := by
    calc
      _ ≤ g.edist x p + g.edist p y := edist_triangle x p y
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := by
        exact add_le_add (by rw [show g.edist x p = g.edist p x from edist_comm x p]; exact hx.le) hy.le
      _ = ENNReal.ofReal (2*r) := by rw [← ENNReal.ofReal_add hr.le (by positivity)]; congr 1; ring
  have hfin : g.edist x y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxy
  have hlen : (g.edist x y).toReal ≤ 2*r :=
    (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hxy |>.trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hcompact : IsCompact (closure (g.ball x (4*r))) :=
    (g.isCompact_closedBall_of_metricComplete hc x (4*r)).of_isClosed_subset
      isClosed_closure (closure_minimal (fun z hz => (show g.edist x z < ENNReal.ofReal (4*r) from hz).le)
        (isClosed_le (continuous_const.edist continuous_id) continuous_const))
  obtain ⟨ε,hε,γ,hγ,hγ0,hγ1,hmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball x y (by positivity : 0 < 4*r)
      hcompact (hxy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr
        (by linarith)))
  have hI : Icc (0:ℝ) 1 ⊆ Ioo (-ε) (1+ε) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have h0 := hI (show (0:ℝ) ∈ Icc 0 1 by simp)
  obtain ⟨C,hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hv := (hγ.hasDerivAt_chart_at h0 x (by
    simpa only [hγ0] using mem_extChartAt_source x)).1
  have hC0 : g.tangentNorm x (deriv (fun s => extChartAt (𝓡 n) x (γ s)) 0) = C := by
    simpa only [RiemannianMetric.chartCoefficients_self, RiemannianMetric.tangentNorm] using
      (hγ.tangentNorm_initial h0 hγ0 hv).symm.trans (hC 0 h0)
  have hCd : (C:ℝ) = (g.edist x y).toReal := by
    have he := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
    rw [hC0] at he
    simpa only [ENNReal.toReal_ofReal C.coe_nonneg] using congrArg ENNReal.toReal he
  refine ⟨ε,hε,γ,hγ,hγ0,hγ1,hlen,hfin,fun s hs => ⟨?_,(hC s (hI hs)).trans hCd⟩⟩
  have hxs : g.edist x (γ s) ≤ g.edist x y := by
    have he := hmin 0 (by simp) s hs
    rw [hγ0,zero_sub,abs_neg,abs_of_nonneg hs.1] at he
    rw [he]
    exact mul_le_of_le_one_left' (by exact_mod_cast hs.2)
  calc
    _ ≤ g.edist p x + g.edist x (γ s) := edist_triangle p x (γ s)
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal (2*r) := add_le_add hx.le (hxs.trans hxy)
    _ = ENNReal.ofReal (3*r) := by rw [← ENNReal.ofReal_add hr.le (by positivity)]; congr 1; ring

private theorem value_bound_along_curve
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {γ : ℝ → M} {I : Set ℝ}
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (hsub : Icc (0:ℝ) 1 ⊆ I) {d : ℝ} (hd : 0 ≤ d)
    (hspeed : ∀ s ∈ Icc (0:ℝ) 1,
      g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ d)
    (hgrad : ∀ s ∈ Icc (0:ℝ) 1, g.tangentNorm (γ s) (g.gradient f (γ s)) ≤ 1) :
    ∀ s ∈ Icc (0:ℝ) 1, |f (γ s) - f (γ 0)| ≤ d := by
  have hderiv (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun t => f (γ t))
        (mvfderiv (𝓡 n) f (γ s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) γ s 1)) s := by
    have hγd := (hγ.contMDiffAt (hI.mem_nhds (hsub hs))).mdifferentiableAt
      (by simp)
    exact ((hf.mdifferentiable (by simp) (γ s)).hasMFDerivAt.comp s
      hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hbound (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖mvfderiv (𝓡 n) f (γ s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) γ s 1)‖ ≤ d := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    rw [Real.norm_eq_abs, ← g.inner_gradient]
    calc
      _ ≤ g.tangentNorm (γ s) (g.gradient f (γ s)) *
          g.tangentNorm (γ s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) γ s 1) :=
        abs_real_inner_le_norm (g.gradient f (γ s))
          (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) γ s 1)
      _ ≤ 1 * g.tangentNorm (γ s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) γ s 1) :=
        mul_le_mul_of_nonneg_right (hgrad s hs) (Real.sqrt_nonneg _)
      _ ≤ d := by simpa only [one_mul] using hspeed s hs
  intro s hs
  have he := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hderiv z hz).hasDerivWithinAt) hbound
    (by simp : (0:ℝ) ∈ Icc 0 1) hs
  have he' : |f (γ s) - f (γ 0)| ≤ d * s := by
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hs.1] using he
  exact he'.trans (mul_le_of_le_one_right hd hs.2)
end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData
private theorem lift_retracted_curve
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) M] [IsManifold (𝓡 (n+1)) ∞ M]
    (g : RiemannianMetric (n+1) M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ f) (U : TopologicalSpace.Opens M)
    (hreg : ∀ y ∈ U, mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) f y ≠ 0)
    (t : ℝ) (x : openLevelSet f U t)
    {γ : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 (n+1)) ∞ γ I)
    {Q : M → M} {V : Set M} (hV : IsOpen V)
    (hQ : ContMDiffOn (𝓡 (n+1)) (𝓡 (n+1)) ∞ Q V)
    (hlevel : ∀ z ∈ V, Q z ∈ U ∧ f (Q z) = t) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg n t
    letI := isManifold_openLevelSet hf U hreg n t
    let J := I ∩ γ ⁻¹' V
    ∃ Γ : ℝ → openLevelSet f U t,
      ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 n) ∞ Γ J ∧
      ∀ s ∈ J, openLevelIncl f U t (Γ s) = Q (γ s) ∧
        (g.regularLevelMetric hf U hreg t).tangentNorm (Γ s)
            (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) Γ s 1) =
          g.tangentNorm (Q (γ s))
            (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) Q (γ s)
              (mfderiv 𝓘(ℝ,ℝ) (𝓡 (n+1)) γ s 1)) := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n t
  let := isManifold_openLevelSet hf U hreg n t
  let J := I ∩ γ ⁻¹' V
  have hJo : IsOpen J := hγ.continuousOn.isOpen_inter_preimage hI hV
  let Γ : ℝ → openLevelSet f U t := fun s =>
    if hs : s ∈ J then ⟨⟨Q (γ s),(hlevel _ hs.2).1⟩,(hlevel _ hs.2).2⟩ else x
  have heq (s : ℝ) (hs : s ∈ J) : openLevelIncl f U t (Γ s) = Q (γ s) := by
    simp only [Γ,dif_pos hs,openLevelIncl]
  have hambient : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 (n+1)) ∞
      (openLevelIncl f U t ∘ Γ) J :=
    (hQ.comp (hγ.mono inter_subset_left) (fun _ hs => hs.2)).congr heq
  refine ⟨Γ,(contMDiffOn_into_openLevelSet_iff hf n U hreg t Γ hJo).mpr hambient,?_⟩
  intro s hs
  refine ⟨heq s hs,?_⟩
  rw [g.regularLevelMetric_tangentNorm_mfderiv hf U hreg t Γ
    (hambient.contMDiffAt (hJo.mem_nhds hs)) 1]
  have hevent : openLevelIncl f U t ∘ Γ =ᶠ[𝓝 s] Q ∘ γ :=
    eventually_nhds_iff.mpr ⟨J,heq,hJo,hs⟩
  rw [heq s hs,hevent.mfderiv_eq,mfderiv_comp s
    ((hQ.contMDiffAt (hV.mem_nhds hs.2)).mdifferentiableAt (by simp))
    ((hγ.contMDiffAt (hI.mem_nhds hs.1)).mdifferentiableAt (by simp))]
  rfl
end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData
private theorem paired_retractions
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {g : PoincareConjecture.RiemannianMetric (n + 1) M}
    (D : PoincareConjecture.LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ h)
    (U : TopologicalSpace.Opens M) {H r : ℝ}
    (hH : 0 ≤ H) (hr : 0 < r)
    (hfgrad : ∀ y ∈ U, (1 / 2 : ℝ) ≤ g.tangentNorm y (D.gradient f y) ∧
      g.tangentNorm y (D.gradient f y) ≤ 1)
    (hhgrad : ∀ y ∈ U, (1 / 2 : ℝ) ≤ g.tangentNorm y (D.gradient h y) ∧
      g.tangentNorm y (D.gradient h y) ≤ 1)
    (hpair : ∀ y ∈ U,
      g.inner y (D.gradient f y) (D.gradient h y) ≤ -(1 / 8 : ℝ))
    (hfhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 (n + 1)) y,
      mvfderiv (𝓡 (n + 1)) f y v = 0 →
        D.hessian f y v v ≤ H * g.inner y v v)
    (hhhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 (n + 1)) y,
      mvfderiv (𝓡 (n + 1)) h y v = 0 →
        D.hessian h y v v ≤ H * g.inner y v v)
    (hcomplete : PoincareConjecture.MetricComplete g) (p : M)
    (hball : {y | g.edist p y ≤ ENNReal.ofReal (40 * r)} ⊆ U) (t : ℝ) :
    ∃ (Vneg Vpos : Set M) (Qneg Qpos : M → M),
      IsOpen Vneg ∧ IsOpen Vpos ∧
      {z | g.edist p z ≤ ENNReal.ofReal (3*r) ∧ f z ∈ Icc (t-2*r) t} ⊆ Vneg ∧
      {z | g.edist p z ≤ ENNReal.ofReal (3*r) ∧ f z ∈ Icc t (t+2*r)} ⊆ Vpos ∧
      ContMDiffOn (𝓡 (n+1)) (𝓡 (n+1)) ∞ Qneg Vneg ∧
      ContMDiffOn (𝓡 (n+1)) (𝓡 (n+1)) ∞ Qpos Vpos ∧
      (∀ z ∈ Vneg, Qneg z ∈ U ∧ f (Qneg z) = t ∧ (f z = t → Qneg z = z)) ∧
      (∀ z ∈ Vpos, Qpos z ∈ U ∧ f (Qpos z) = t ∧ (f z = t → Qpos z = z)) ∧
      (∀ z, g.edist p z ≤ ENNReal.ofReal (3*r) → f z ∈ Icc (t-2*r) t →
        ∀ v, g.tangentNorm (Qneg z) (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) Qneg z v) ≤
          (9 * Real.exp (64*H*r)) * g.tangentNorm z v) ∧
      (∀ z, g.edist p z ≤ ENNReal.ofReal (3*r) → f z ∈ Icc t (t+2*r) →
        ∀ v, g.tangentNorm (Qpos z) (mfderiv (𝓡 (n+1)) (𝓡 (n+1)) Qpos z v) ≤
          (9 * Real.exp (64*H*r)) * g.tangentNorm z v) := by
  obtain ⟨Vneg,Qneg,hVneg,hKneg,hVnegU,hQneg,hneg,hbneg⟩ :=
    D.exists_positive_level_retraction_on_closedBall
      U.isOpen hf.contMDiffOn (by norm_num : (0:ℝ)<1/2) hH
      (fun z hz => (hfgrad z hz).1) hfhess hcomplete p
      (by positivity : 0≤3*r) (by positivity : 0≤2*r)
      (by norm_num; linarith : 3*r+(2*r)/(1/2)≤40*r) hball t
  obtain ⟨Vpos,δ,Φ,σ,hVpos,hKpos,hVposU,hδ,hΦ,hzero,horbit,hσ,hQpos,hhit,hbpos⟩ :=
    D.exists_uniform_level_retraction_on_closedBall
      U.isOpen hf.contMDiffOn hh.contMDiffOn (by norm_num : (0:ℝ)<1/2) hH
      (by norm_num : (0:ℝ)<1/8) (fun z hz => (hhgrad z hz).1)
      (fun z hz => (hhgrad z hz).2) (fun z hz => (hfgrad z hz).2)
      hhhess hpair hcomplete p (by positivity : 0≤3*r) (by positivity : 0≤16*r)
      (by norm_num; linarith : 3*r+(16*r)/(1/2)≤40*r) hball t
  let Qpos : M → M := fun z => Φ (σ z,z)
  have hposdom : {z | g.edist p z ≤ ENNReal.ofReal (3*r) ∧ f z ∈ Icc t (t+2*r)} ⊆ Vpos := by
    rintro z ⟨hzd,hzf⟩
    exact hKpos ⟨hzd,hzf.1,by norm_num; linarith [hzf.2]⟩
  refine ⟨Vneg,Vpos,Qneg,Qpos,hVneg,hVpos,hKneg,hposdom,hQneg,hQpos,hneg,?_,?_,?_⟩
  · intro z hz
    exact ⟨(horbit z hz).1 _ (hhit z hz).1,(hhit z hz).2.1,(hhit z hz).2.2.2.2⟩
  · intro z hzd hzf v
    apply ((hbneg z hzd hzf).2 v).trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    calc
      _ ≤ Real.exp (64*H*r) := by
        apply Real.exp_le_exp.mpr
        norm_num
        nlinarith [mul_le_mul_of_nonneg_left (show t-f z≤2*r by linarith [hzf.1]) hH,
          mul_nonneg hH hr.le]
      _ ≤ 9 * Real.exp (64*H*r) := by nlinarith [Real.exp_pos (64*H*r)]
  · intro z hzd hzf v
    have hzK : g.edist p z ≤ ENNReal.ofReal (3*r) ∧ t ≤ f z ∧ f z ≤ t+(1/8)*(16*r) :=
      ⟨hzd,hzf.1,by norm_num; linarith [hzf.2]⟩
    apply ((hbpos z hzK).2 v).trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left (show f z-t≤2*r by linarith [hzf.2]) hH]

end PoincareConjecture.LeviCivitaData


theorem PoincareConjecture.LeviCivitaData.regularLevel_edist_le_of_opposite_gradients
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {g : PoincareConjecture.RiemannianMetric (n + 1) M}
    (D : PoincareConjecture.LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ h)
    (U : TopologicalSpace.Opens M) {H r : ℝ}
    (hH : 0 ≤ H) (hr : 0 < r)
    (hfgrad : ∀ y ∈ U, (1 / 2 : ℝ) ≤ g.tangentNorm y (D.gradient f y) ∧
      g.tangentNorm y (D.gradient f y) ≤ 1)
    (hhgrad : ∀ y ∈ U, (1 / 2 : ℝ) ≤ g.tangentNorm y (D.gradient h y) ∧
      g.tangentNorm y (D.gradient h y) ≤ 1)
    (hpair : ∀ y ∈ U,
      g.inner y (D.gradient f y) (D.gradient h y) ≤ -(1 / 8 : ℝ))
    (hfhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 (n + 1)) y,
      mvfderiv (𝓡 (n + 1)) f y v = 0 →
        D.hessian f y v v ≤ H * g.inner y v v)
    (hhhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 (n + 1)) y,
      mvfderiv (𝓡 (n + 1)) h y v = 0 →
        D.hessian h y v v ≤ H * g.inner y v v)
    (hcomplete : PoincareConjecture.MetricComplete g) (p : M)
    (hball : {y | g.edist p y ≤ ENNReal.ofReal (40 * r)} ⊆ U) :
    ∃ hreg : ∀ y ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f y ≠ 0,
      ∀ t : ℝ,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := Poincare.Geometry.Manifold.RegularLevel.openLevelSetChartedSpace hf U hreg n t
        letI := Poincare.Geometry.Manifold.RegularLevel.isManifold_openLevelSet hf U hreg n t
        let L := Poincare.Geometry.Manifold.RegularLevel.openLevelSet f U t
        let incl := Poincare.Geometry.Manifold.RegularLevel.openLevelIncl f U t
        let gL := g.regularLevelMetric hf U hreg t
        ∀ x y : L, incl x ∈ g.ball p r → incl y ∈ g.ball p r →
          gL.edist x y ≤ ENNReal.ofReal (9 * Real.exp (64 * H * r)) *
            g.edist (incl x) (incl y) ∧ Joined x y := by
  classical
  have hreg : ∀ y ∈ U, mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) f y ≠ 0 := by
    intro y hy
    apply (g.tangentNorm_gradient_pos_iff f y).mp
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hfgrad y hy).1
  refine ⟨hreg,fun t => ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n t
  let := isManifold_openLevelSet hf U hreg n t
  let L := openLevelSet f U t
  let incl := openLevelIncl f U t
  let gL := g.regularLevelMetric hf U hreg t
  dsimp only
  intro x y hx hy
  have hxt : f (incl x) = t := x.2
  have hyt : f (incl y) = t := y.2
  obtain ⟨ε,hε,γ,hγ,hγ0,hγ1,hlen,hfin,hbounds⟩ :=
    PoincareConjecture.LeviCivitaData.short_geodesic g hcomplete p hr (incl x) (incl y) hx hy
  have hI : Icc (0:ℝ) 1 ⊆ Ioo (-ε) (1+ε) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have hγsmooth : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡 (n+1)) ∞ γ (Ioo (-ε) (1+ε)) :=
    fun s hs => (PoincareConjecture.Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ hs).contMDiffWithinAt
  have hpathU (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : γ s ∈ U :=
    hball ((hbounds s hs).1.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hvalue : ∀ s ∈ Icc (0:ℝ) 1, |f (γ s)-t| ≤ 2*r := by
    intro s hs
    have he := PoincareConjecture.LeviCivitaData.value_bound_along_curve g hf isOpen_Ioo
      hγsmooth hI ENNReal.toReal_nonneg (fun z hz => (hbounds z hz).2.le)
      (fun z hz => (hfgrad _ (hpathU z hz)).2) s hs
    simpa only [hγ0,hxt] using he.trans hlen
  obtain ⟨Vneg,Vpos,Qneg,Qpos,hVneg,hVpos,hKneg,hKpos,hQneg,hQpos,hneg,hpos,hbneg,hbpos⟩ :=
    PoincareConjecture.LeviCivitaData.paired_retractions D hf hh U hH hr hfgrad hhgrad hpair
      hfhess hhhess hcomplete p hball t
  let Ineg := Ioo (-ε) (1+ε) ∩ γ ⁻¹' Vneg
  let Ipos := Ioo (-ε) (1+ε) ∩ γ ⁻¹' Vpos
  have hIneg : IsOpen Ineg := hγsmooth.continuousOn.isOpen_inter_preimage isOpen_Ioo hVneg
  have hIpos : IsOpen Ipos := hγsmooth.continuousOn.isOpen_inter_preimage isOpen_Ioo hVpos
  obtain ⟨Γneg,hΓneg,hliftneg⟩ :=
    PoincareConjecture.LeviCivitaData.lift_retracted_curve g hf U hreg t x isOpen_Ioo
      hγsmooth hVneg hQneg (fun z hz => ⟨(hneg z hz).1,(hneg z hz).2.1⟩)
  obtain ⟨Γpos,hΓpos,hliftpos⟩ :=
    PoincareConjecture.LeviCivitaData.lift_retracted_curve g hf U hreg t x isOpen_Ioo
      hγsmooth hVpos hQpos (fun z hz => ⟨(hpos z hz).1,(hpos z hz).2.1⟩)
  let q : ℝ → ℝ := fun s => f (γ s)-t
  let C : ℝ := 9*Real.exp (64*H*r)
  let d : ℝ := (g.edist (incl x) (incl y)).toReal
  have hq : ContinuousOn q (Icc (0:ℝ) 1) :=
    (hf.continuous.comp_continuousOn (hγsmooth.continuousOn.mono hI)).sub continuousOn_const
  have hnegband (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (hqs : q s ≤ 0) :
      f (γ s) ∈ Icc (t-2*r) t := by
    have he := (abs_le.mp (hvalue s hs)).1
    dsimp only [q] at hqs
    exact ⟨by linarith,by linarith⟩
  have hposband (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (hqs : 0 ≤ q s) :
      f (γ s) ∈ Icc t (t+2*r) := by
    have he := (abs_le.mp (hvalue s hs)).2
    dsimp only [q] at hqs
    exact ⟨by linarith,by linarith⟩
  have hdomneg (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (hqs : q s ≤ 0) : s ∈ Ineg :=
    ⟨hI hs,hKneg ⟨(hbounds s hs).1,hnegband s hs hqs⟩⟩
  have hdompos (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (hqs : 0 ≤ q s) : s ∈ Ipos :=
    ⟨hI hs,hKpos ⟨(hbounds s hs).1,hposband s hs hqs⟩⟩
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have heq (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (hqs : q s = 0) : Γneg s = Γpos s := by
    apply (isEmbedding_openLevelIncl f U t).injective
    rw [(hliftneg s (hdomneg s hs hqs.le)).1,(hliftpos s (hdompos s hs hqs.ge)).1]
    have hft : f (γ s) = t := sub_eq_zero.mp hqs
    rw [(hneg _ (hdomneg s hs hqs.le).2).2.2 hft,
      (hpos _ (hdompos s hs hqs.ge).2).2.2 hft]
  have hspeedneg (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (hqs : q s ≤ 0) :
      gL.tangentNorm (Γneg s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) Γneg s 1) ≤ C*d := by
    rw [(hliftneg s (hdomneg s hs hqs)).2]
    simpa only [(hbounds s hs).2] using
      hbneg (γ s) (hbounds s hs).1 (hnegband s hs hqs)
        (mfderiv 𝓘(ℝ,ℝ) (𝓡 (n+1)) γ s 1)
  have hspeedpos (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (hqs : 0 ≤ q s) :
      gL.tangentNorm (Γpos s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 n) Γpos s 1) ≤ C*d := by
    rw [(hliftpos s (hdompos s hs hqs)).2]
    simpa only [(hbounds s hs).2] using
      hbpos (γ s) (hbounds s hs).1 (hposband s hs hqs)
        (mfderiv 𝓘(ℝ,ℝ) (𝓡 (n+1)) γ s 1)
  have hq0 : q 0 = 0 := by simp only [q,hγ0,hxt,sub_self]
  have hq1 : q 1 = 0 := by simp only [q,hγ1,hyt,sub_self]
  have hΓ0 : Γneg 0 = x := by
    apply (isEmbedding_openLevelIncl f U t).injective
    rw [(hliftneg 0 (hdomneg 0 (by simp) hq0.le)).1,
      (hneg _ (hdomneg 0 (by simp) hq0.le).2).2.2 (by simpa only [hγ0] using hxt)]
    exact hγ0
  have hΓ1 : Γneg 1 = y := by
    apply (isEmbedding_openLevelIncl f U t).injective
    rw [(hliftneg 1 (hdomneg 1 (by simp) hq1.le)).1,
      (hneg _ (hdomneg 1 (by simp) hq1.le).2).2.2 (by simpa only [hγ1] using hyt)]
    exact hγ1
  have hdist := gL.edist_piecewise_curve_le_of_speed_le zero_le_one (mul_nonneg hC hd)
    q hq Γneg Γpos hIneg hIpos hΓneg hΓpos hdomneg hdompos heq hspeedneg hspeedpos
  dsimp only at hdist
  simp only [hq0,hq1,le_refl,ite_true,hΓ0,hΓ1,sub_zero,mul_one] at hdist
  have hbound : gL.edist x y ≤ ENNReal.ofReal C * g.edist (incl x) (incl y) := by
    simpa only [ENNReal.ofReal_mul hC,d,ENNReal.ofReal_toReal hfin] using hdist
  refine ⟨hbound,?_⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : L → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  have hfinite : gL.edist x y < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top)
  obtain ⟨η,hη0,hη1,hη,_⟩ := Manifold.exists_lt_of_riemannianEDist_lt hfinite
  exact ⟨Path.ofLine hη.continuousOn hη0 hη1⟩
