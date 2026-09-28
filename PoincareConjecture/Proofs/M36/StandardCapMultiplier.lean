import PoincareConjecture.Proofs.M36.StandardCapPlanes
import PoincareConjecture.Proofs.M36.RadialWeights
import PoincareConjecture.Proofs.M36.ProfileDerivatives
import PoincareConjecture.Proofs.M36.RadialDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle
open Filter Set Topology

namespace PoincareConjecture.M36

private noncomputable def capMultiplierProfile (g₀ : StandardInitialMetric)
    (C q epsilon r t : ℝ) : ℝ :=
  let A := g₀.cylindrical_end.radius + 4
  tipCutoff A r (A - t) * conformalFactor C q epsilon (A - t) +
    (1 - tipCutoff A r (A - t)) * conformalFactor C q epsilon A

noncomputable def standardCapConformalProfile (g₀ : StandardInitialMetric)
    (C q epsilon r t : ℝ) : ℝ :=
  -Real.log (capMultiplierProfile g₀ C q epsilon r t) / 2

noncomputable def standardCapConformalExponent (g₀ : StandardInitialMetric)
    (C q epsilon r : ℝ) (x : StandardCapSpace) : ℝ :=
  -Real.log (radialConformalMultiplier g₀ C q epsilon r x) / 2

private theorem capMultiplierProfile_pos (g₀ : StandardInitialMetric)
    (C q epsilon r t : ℝ) : 0 < capMultiplierProfile g₀ C q epsilon r t := by
  let A := g₀.cylindrical_end.radius + 4
  have hb0 := tipCutoff_nonneg A r (A - t)
  have hb1 := tipCutoff_le_one A r (A - t)
  have hE := conformalFactor_pos C q epsilon (A - t)
  have hE0 := conformalFactor_pos C q epsilon A
  change 0 < tipCutoff A r (A - t) * conformalFactor C q epsilon (A - t) +
    (1 - tipCutoff A r (A - t)) * conformalFactor C q epsilon A
  rcases hb0.lt_or_eq with hb | hb
  · exact add_pos_of_pos_of_nonneg (mul_pos hb hE)
      (mul_nonneg (sub_nonneg.mpr hb1) hE0.le)
  · rw [← hb]
    simpa using hE0

private theorem capMultiplierProfile_joint_contDiff (g₀ : StandardInitialMetric)
    (C q r : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => capMultiplierProfile g₀ C q p.1 r p.2) := by
  let A := g₀.cylindrical_end.radius + 4
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => A - p.2) :=
    contDiff_const.sub contDiff_snd
  have hb : ContDiff ℝ ∞ (fun p : ℝ × ℝ => tipCutoff A r (A - p.2)) :=
    (tipCutoff_contDiff A r).comp hs
  have hf : ContDiff ℝ ∞ (fun p : ℝ × ℝ => smoothProfile C q p.1 (A - p.2)) :=
    (contDiff_const.mul contDiff_fst).mul (expNegInvGlue.contDiff.comp (hs.div_const q))
  have hf0 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => smoothProfile C q p.1 A) :=
    (contDiff_const.mul contDiff_fst).mul contDiff_const
  exact (hb.mul (contDiff_const.mul hf).exp).add
    ((contDiff_const.sub hb).mul (contDiff_const.mul hf0).exp)

theorem standardCapConformalProfile_joint_contDiff (g₀ : StandardInitialMetric)
    (C q r : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => standardCapConformalProfile g₀ C q p.1 r p.2) :=
  ((capMultiplierProfile_joint_contDiff g₀ C q r).log
    (fun p => (capMultiplierProfile_pos g₀ C q p.1 r p.2).ne')).neg.div_const 2

theorem standardCapConformalProfile_contDiff (g₀ : StandardInitialMetric)
    (C q epsilon r : ℝ) : ContDiff ℝ ∞ (standardCapConformalProfile g₀ C q epsilon r) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (epsilon, t)) :=
    contDiff_const.prodMk contDiff_id
  exact (standardCapConformalProfile_joint_contDiff g₀ C q r).comp
    (f := fun t : ℝ => (epsilon, t)) hs

private theorem cap_partial_deriv_contDiff {h : ℝ → ℝ → ℝ}
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (h p.1) p.2) := by
  have hh' : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => h p.1)) :=
    hh.comp ((contDiff_fst.fst).prodMk contDiff_snd)
  exact hh'.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem standardCapConformalProfile_deriv_joint_contDiff (g₀ : StandardInitialMetric)
    (C q r : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (standardCapConformalProfile g₀ C q p.1 r) p.2) :=
  cap_partial_deriv_contDiff (h := fun e t => standardCapConformalProfile g₀ C q e r t)
    (standardCapConformalProfile_joint_contDiff g₀ C q r)

theorem standardCapConformalProfile_second_deriv_joint_contDiff (g₀ : StandardInitialMetric)
    (C q r : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      deriv (deriv (standardCapConformalProfile g₀ C q p.1 r)) p.2) :=
  cap_partial_deriv_contDiff
    (h := fun e t => deriv (standardCapConformalProfile g₀ C q e r) t)
    (standardCapConformalProfile_deriv_joint_contDiff g₀ C q r)

theorem standardCapConformalExponent_contDiff (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (standardCapConformalExponent g₀ C q epsilon r) :=
  ((radialConformalMultiplier_contDiff g₀ C q epsilon hr).log
    (fun x => (radialConformalMultiplier_pos g₀ C q epsilon r x).ne')).neg.div_const 2

theorem standardCapConformalExponent_eq_profile (g₀ : StandardInitialMetric)
    (C q epsilon r : ℝ) (x : StandardCapSpace) :
    standardCapConformalExponent g₀ C q epsilon r x =
      standardCapConformalProfile g₀ C q epsilon r (radialArclength g₀ ‖x‖) := rfl

theorem standardCapConformalExponent_exp (g₀ : StandardInitialMetric)
    (C q epsilon r : ℝ) (x : StandardCapSpace) :
    Real.exp (-2 * standardCapConformalExponent g₀ C q epsilon r x) =
      radialConformalMultiplier g₀ C q epsilon r x := by
  unfold standardCapConformalExponent
  rw [show -2 * (-Real.log (radialConformalMultiplier g₀ C q epsilon r x) / 2) =
    Real.log (radialConformalMultiplier g₀ C q epsilon r x) by ring]
  exact Real.exp_log (radialConformalMultiplier_pos g₀ C q epsilon r x)

theorem standardCapConformalProfile_zero (g₀ : StandardInitialMetric)
    (C q r : ℝ) : standardCapConformalProfile g₀ C q 0 r = fun _ => 0 := by
  funext t
  simp [standardCapConformalProfile, capMultiplierProfile, conformalFactor, smoothProfile]

theorem standardCapConformalProfile_deriv_zero (g₀ : StandardInitialMetric)
    (C q r t : ℝ) : deriv (standardCapConformalProfile g₀ C q 0 r) t = 0 := by
  rw [standardCapConformalProfile_zero]
  simp

theorem standardCapConformalProfile_second_deriv_zero (g₀ : StandardInitialMetric)
    (C q r t : ℝ) : deriv (deriv (standardCapConformalProfile g₀ C q 0 r)) t = 0 := by
  rw [standardCapConformalProfile_zero]
  simp

theorem standardCapConformalProfile_jets_eventually_small (g₀ : StandardInitialMetric)
    (C q r : ℝ) {K : Set ℝ} (hK : IsCompact K) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ epsilon in 𝓝 (0 : ℝ), ∀ t ∈ K,
      |standardCapConformalProfile g₀ C q epsilon r t| < eta ∧
      |deriv (standardCapConformalProfile g₀ C q epsilon r) t| < eta ∧
      |deriv (deriv (standardCapConformalProfile g₀ C q epsilon r)) t| < eta := by
  apply hK.eventually_forall_of_forall_eventually
  intro t _
  have h0 := ((standardCapConformalProfile_joint_contDiff g₀ C q r).continuous.continuousAt
    (x := ((0 : ℝ), t))).abs
  have h1 := ((standardCapConformalProfile_deriv_joint_contDiff g₀ C q r).continuous.continuousAt
    (x := ((0 : ℝ), t))).abs
  have h2 := ((standardCapConformalProfile_second_deriv_joint_contDiff
    g₀ C q r).continuous.continuousAt (x := ((0 : ℝ), t))).abs
  have hz0 : |standardCapConformalProfile g₀ C q 0 r t| < eta := by
    simpa only [standardCapConformalProfile_zero, abs_zero] using heta
  have hz1 : |deriv (standardCapConformalProfile g₀ C q 0 r) t| < eta := by
    simpa only [standardCapConformalProfile_deriv_zero, abs_zero] using heta
  have hz2 : |deriv (deriv (standardCapConformalProfile g₀ C q 0 r)) t| < eta := by
    simpa only [standardCapConformalProfile_second_deriv_zero, abs_zero] using heta
  filter_upwards [h0.eventually (gt_mem_nhds hz0), h1.eventually (gt_mem_nhds hz1),
    h2.eventually (gt_mem_nhds hz2)] with p hp0 hp1 hp2
  exact ⟨hp0, hp1, hp2⟩

theorem standardCapConformalProfile_jets_small (g₀ : StandardInitialMetric)
    (C q r : ℝ) {K : Set ℝ} (hK : IsCompact K) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, |epsilon| < delta → ∀ t ∈ K,
      |standardCapConformalProfile g₀ C q epsilon r t| < eta ∧
      |deriv (standardCapConformalProfile g₀ C q epsilon r) t| < eta ∧
      |deriv (deriv (standardCapConformalProfile g₀ C q epsilon r)) t| < eta := by
  obtain ⟨delta, hdelta, hbound⟩ := Metric.eventually_nhds_iff.mp
    (standardCapConformalProfile_jets_eventually_small g₀ C q r hK heta)
  refine ⟨delta, hdelta, fun epsilon hepsilon => hbound ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hepsilon

theorem standardCapConformalProfile_eq_tip (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r t : ℝ} (hr : 0 < r) (ht : t ≤ r / 2) :
    standardCapConformalProfile g₀ C q epsilon r t =
      smoothProfile C q epsilon (g₀.cylindrical_end.radius + 4) := by
  have hb : tipCutoff (g₀.cylindrical_end.radius + 4) r
      (g₀.cylindrical_end.radius + 4 - t) = 0 :=
    tipCutoff_eq_zero hr (by linarith)
  simp only [standardCapConformalProfile, capMultiplierProfile, hb,
    zero_mul, sub_zero, one_mul, zero_add, conformalFactor, Real.log_exp]
  ring

theorem standardCapConformalProfile_eq_outer (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r t : ℝ} (hr : 0 < r) (ht : 3 * r / 4 ≤ t) :
    standardCapConformalProfile g₀ C q epsilon r t =
      smoothProfile C q epsilon (g₀.cylindrical_end.radius + 4 - t) := by
  have hb : tipCutoff (g₀.cylindrical_end.radius + 4) r
      (g₀.cylindrical_end.radius + 4 - t) = 1 :=
    tipCutoff_eq_one hr (by linarith)
  simp only [standardCapConformalProfile, capMultiplierProfile, hb,
    one_mul, sub_self, zero_mul, add_zero, conformalFactor, Real.log_exp]
  ring

theorem standardCapConformalProfile_germ_tip (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r t : ℝ} (hr : 0 < r) (ht : t < r / 2) :
    standardCapConformalProfile g₀ C q epsilon r =ᶠ[𝓝 t]
      fun _ => smoothProfile C q epsilon (g₀.cylindrical_end.radius + 4) := by
  filter_upwards [gt_mem_nhds ht] with u hu
  exact standardCapConformalProfile_eq_tip g₀ C q epsilon hr hu.le

theorem standardCapConformalProfile_germ_outer (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r t : ℝ} (hr : 0 < r) (ht : 3 * r / 4 < t) :
    standardCapConformalProfile g₀ C q epsilon r =ᶠ[𝓝 t]
      fun u => smoothProfile C q epsilon (g₀.cylindrical_end.radius + 4 - u) := by
  filter_upwards [lt_mem_nhds ht] with u hu
  exact standardCapConformalProfile_eq_outer g₀ C q epsilon hr hu.le

private theorem cap_deriv_reflection {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (A t : ℝ) : deriv (fun u => h (A - u)) t = -deriv h (A - t) := by
  have hd := ((hh.differentiable (by simp) (A - t)).hasDerivAt.comp t
    ((hasDerivAt_const t A).sub (hasDerivAt_id t))).deriv
  simpa only [Function.comp_def, sub_self, zero_sub, mul_neg_one] using hd

private theorem cap_second_deriv_reflection {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (A t : ℝ) : deriv (deriv (fun u => h (A - u))) t =
      deriv (deriv h) (A - t) := by
  have hfun : deriv (fun u => h (A - u)) = fun u => -deriv h (A - u) :=
    funext (cap_deriv_reflection hh A)
  rw [hfun, deriv.fun_neg, cap_deriv_reflection (contDiff_infty_iff_deriv.mp hh).2]
  exact neg_neg _

theorem standardCapConformalProfile_deriv_tip (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r t : ℝ} (hr : 0 < r) (ht : t < r / 2) :
    deriv (standardCapConformalProfile g₀ C q epsilon r) t = 0 := by
  rw [(standardCapConformalProfile_germ_tip g₀ C q epsilon hr ht).deriv_eq]
  simp

theorem standardCapConformalProfile_second_deriv_tip (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r t : ℝ} (hr : 0 < r) (ht : t < r / 2) :
    deriv (deriv (standardCapConformalProfile g₀ C q epsilon r)) t = 0 := by
  rw [(standardCapConformalProfile_germ_tip g₀ C q epsilon hr ht).deriv.deriv_eq]
  simp

theorem standardCapConformalProfile_deriv_outer (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r t : ℝ} (hr : 0 < r) (ht : 3 * r / 4 < t) :
    deriv (standardCapConformalProfile g₀ C q epsilon r) t =
      -deriv (smoothProfile C q epsilon) (g₀.cylindrical_end.radius + 4 - t) := by
  rw [(standardCapConformalProfile_germ_outer g₀ C q epsilon hr ht).deriv_eq]
  exact cap_deriv_reflection (smoothProfile_contDiff C q epsilon) _ t

theorem standardCapConformalProfile_second_deriv_outer (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r t : ℝ} (hr : 0 < r) (ht : 3 * r / 4 < t) :
    deriv (deriv (standardCapConformalProfile g₀ C q epsilon r)) t =
      deriv (deriv (smoothProfile C q epsilon)) (g₀.cylindrical_end.radius + 4 - t) := by
  rw [(standardCapConformalProfile_germ_outer g₀ C q epsilon hr ht).deriv.deriv_eq]
  exact cap_second_deriv_reflection (smoothProfile_contDiff C q epsilon) _ t

theorem sectionalCurvature_smul {g : RiemannianMetric 3 StandardCapSpace}
    (D : LeviCivitaData g) (x u v : StandardCapSpace) {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    D.sectionalCurvature x (a • u) (b • v) = D.sectionalCurvature x u v := by
  obtain ⟨T, hT⟩ := (M04.isSmoothCovariantTensor_riemannEvaluation D).1 x
  have hscale := T.map_smul_univ ![a, b, a, b] ![u, v, u, v]
  have he : (fun i : Fin 4 => ![a, b, a, b] i • ![u, v, u, v] i) =
      ![a • u, b • v, a • u, b • v] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hscale
  simp only [← hT, LeviCivitaData.riemannEvaluation, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_succ,
    Fin.prod_univ_succ, Fin.prod_univ_zero, smul_eq_mul, mul_one] at hscale
  have hnum : D.curvatureTensor x (a • u) (b • v) (a • u) (b • v) =
      (a ^ 2 * b ^ 2) * D.curvatureTensor x u v u v := by
    rw [hscale]
    ring
  have hden : g.inner x (a • u) (a • u) * g.inner x (b • v) (b • v) -
      (g.inner x (a • u) (b • v)) ^ 2 =
      (a ^ 2 * b ^ 2) * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  unfold LeviCivitaData.sectionalCurvature
  rw [hnum, hden]
  exact mul_div_mul_left _ _ (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb))

theorem positiveScaling_orthonormal_sqrt (g : RiemannianMetric 3 StandardCapSpace)
    (m : StandardCapSpace → ℝ) (hm : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ m)
    (hpos : ∀ x, 0 < m x) (x u v : StandardCapSpace)
    (hpair : LeviCivitaData.IsOrthonormalPair (positiveScaling g m hm hpos) x u v) :
    LeviCivitaData.IsOrthonormalPair g x
      (Real.sqrt (m x) • u) (Real.sqrt (m x) • v) := by
  have he (a b : StandardCapSpace) :
      g.inner x (Real.sqrt (m x) • a) (Real.sqrt (m x) • b) =
        m x * g.inner x a b := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    calc
      Real.sqrt (m x) * (Real.sqrt (m x) * g.inner x a b) =
          (Real.sqrt (m x)) ^ 2 * g.inner x a b := by ring
      _ = m x * g.inner x a b := by rw [Real.sq_sqrt (hpos x).le]
  unfold LeviCivitaData.IsOrthonormalPair at hpair ⊢
  rw [he, he, he]
  exact hpair

theorem standardCap_sectional_multiplier_pos (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r : ℝ} (hr : 0 < r)
    (D : LeviCivitaData (positiveScaling g₀.metric
      (radialConformalMultiplier g₀ C q epsilon r)
      (radialConformalMultiplier_contDiff g₀ C q epsilon hr).contMDiff
      (radialConformalMultiplier_pos g₀ C q epsilon r)))
    {x : StandardCapSpace} (hx : x ≠ 0)
    (hR : 0 < g₀.connection.sectionalCurvature (axisPoint ‖x‖)
      (axisBasis 0) (axisBasis 1) +
        deriv (deriv (standardCapConformalProfile g₀ C q epsilon r))
          (radialArclength g₀ ‖x‖) +
        deriv (standardCapConformalProfile g₀ C q epsilon r) (radialArclength g₀ ‖x‖) *
          (angularRadiusSlope g₀ ‖x‖ / euclideanWarpRadius g₀ ‖x‖))
    (hT : 0 < g₀.connection.sectionalCurvature (axisPoint ‖x‖)
      (axisBasis 1) (axisBasis 2) +
        2 * deriv (standardCapConformalProfile g₀ C q epsilon r) (radialArclength g₀ ‖x‖) *
          (angularRadiusSlope g₀ ‖x‖ / euclideanWarpRadius g₀ ‖x‖) -
        (deriv (standardCapConformalProfile g₀ C q epsilon r) (radialArclength g₀ ‖x‖)) ^ 2)
    (v w : StandardCapSpace)
    (hpair : LeviCivitaData.IsOrthonormalPair (positiveScaling g₀.metric
      (radialConformalMultiplier g₀ C q epsilon r)
      (radialConformalMultiplier_contDiff g₀ C q epsilon hr).contMDiff
      (radialConformalMultiplier_pos g₀ C q epsilon r)) x v w) :
    0 < D.sectionalCurvature x v w := by
  let m := radialConformalMultiplier g₀ C q epsilon r
  have hm := (radialConformalMultiplier_contDiff g₀ C q epsilon hr).contMDiff
  have hpos := radialConformalMultiplier_pos g₀ C q epsilon r
  have hbase := positiveScaling_orthonormal_sqrt g₀.metric m hm hpos x v w hpair
  have hk : 0 < D.sectionalCurvature x (Real.sqrt (m x) • v) (Real.sqrt (m x) • w) := by
    let F := standardCapConformalExponent g₀ C q epsilon r
    have hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F :=
      (standardCapConformalExponent_contDiff g₀ C q epsilon hr).contMDiff
    have hmetric : positiveScaling g₀.metric m hm hpos =
        positiveScaling g₀.metric (fun y => Real.exp (-2 * F y))
          (contMDiff_exp_neg_two hFs) (fun _ => Real.exp_pos _) := by
      have he : (fun y => Real.exp (-2 * F y)) = m :=
        funext (standardCapConformalExponent_exp g₀ C q epsilon r)
      congr 1
      exact he.symm
    revert D
    rw [hmetric]
    intro D
    exact standardCap_sectional_positiveScaling_pos g₀ F hFs D hx
      (standardCapConformalProfile_contDiff g₀ C q epsilon r)
      (Filter.Eventually.of_forall (standardCapConformalExponent_eq_profile g₀ C q epsilon r))
      hR hT _ _ hbase.1 hbase.2.1 hbase.2.2
  rw [sectionalCurvature_smul D x v w
    (Real.sqrt_pos.mpr (hpos x)).ne' (Real.sqrt_pos.mpr (hpos x)).ne'] at hk
  exact hk

private theorem cap_mvfderiv_constant_germ {f : StandardCapSpace → ℝ}
    {x : StandardCapSpace} {c : ℝ} (hf : f =ᶠ[𝓝 x] fun _ => c)
    (v : StandardCapSpace) : mvfderiv (𝓡 3) f x v = 0 := by
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
    NormedSpace.fromTangentSpace]
  change fderiv ℝ f x v = 0
  rw [hf.fderiv_eq]
  simp

private theorem cap_hessian_constant_germ {g : RiemannianMetric 3 StandardCapSpace}
    (D : LeviCivitaData g) {f : StandardCapSpace → ℝ}
    {x : StandardCapSpace} {c : ℝ} (hf : f =ᶠ[𝓝 x] fun _ => c)
    (v w : StandardCapSpace) : D.hessian f x v w = 0 := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin 3))
    (E := (TangentSpace (𝓡 3) : StandardCapSpace → Type _)) (x := x) v
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin 3))
    (E := (TangentSpace (𝓡 3) : StandardCapSpace → Type _)) (x := x) w
  have hzero : (fun y => mvfderiv (𝓡 3) f y (Y y)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hf.eventually_nhds] with y hy
    exact cap_mvfderiv_constant_germ hy (Y y)
  change mvfderiv (𝓡 3) (fun y => mvfderiv (𝓡 3) f y (Y y)) x (X x) -
    mvfderiv (𝓡 3) f x (D.connection Y x (X x)) = 0
  rw [cap_mvfderiv_constant_germ hzero, cap_mvfderiv_constant_germ hf, sub_self]

theorem sectionalCurvature_positiveScaling_constant_germ
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (F : StandardCapSpace → ℝ) (hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hFs) (fun _ => Real.exp_pos _)))
    {x : StandardCapSpace} {c : ℝ} (hF : F =ᶠ[𝓝 x] fun _ => c)
    (v w : StandardCapSpace)
    (hvv : g.inner x v v = 1) (hww : g.inner x w w = 1)
    (hvw : g.inner x v w = 0) :
    D'.sectionalCurvature x v w = Real.exp (2 * F x) * D.sectionalCurvature x v w := by
  rw [sectionalCurvature_positiveScaling_exp g D F hFs D' x v w hvv hww hvw,
    cap_hessian_constant_germ D hF, cap_hessian_constant_germ D hF,
    D.inner_gradient, cap_mvfderiv_constant_germ hF,
    cap_mvfderiv_constant_germ hF, cap_mvfderiv_constant_germ hF]
  ring

theorem positiveScaling_const_sectional_pos {g : RiemannianMetric 3 StandardCapSpace}
    (D : LeviCivitaData g) {c : ℝ} (hc : 0 < c)
    (D' : LeviCivitaData (positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)))
    (x : StandardCapSpace)
    (hK : ∀ v w : StandardCapSpace, LeviCivitaData.IsOrthonormalPair g x v w →
      0 < D.sectionalCurvature x v w)
    (v w : StandardCapSpace)
    (hpair : LeviCivitaData.IsOrthonormalPair
      (positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)) x v w) :
    0 < D'.sectionalCurvature x v w := by
  have hbase := positiveScaling_orthonormal_sqrt g (fun _ => c) contMDiff_const
    (fun _ => hc) x v w hpair
  let F : StandardCapSpace → ℝ := fun _ => -Real.log c / 2
  have hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F := contMDiff_const
  have hmetric : positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc) =
      positiveScaling g (fun y => Real.exp (-2 * F y))
        (contMDiff_exp_neg_two hFs) (fun _ => Real.exp_pos _) := by
    have he : (fun y => Real.exp (-2 * F y)) = fun _ => c := by
      funext y
      change Real.exp (-2 * (-Real.log c / 2)) = c
      rw [show -2 * (-Real.log c / 2) = Real.log c by ring, Real.exp_log hc]
    congr 1
    exact he.symm
  have hpos : 0 < D'.sectionalCurvature x (Real.sqrt c • v) (Real.sqrt c • w) := by
    revert D'
    rw [hmetric]
    intro D'
    rw [sectionalCurvature_positiveScaling_constant_germ g D F hFs D'
      (Filter.Eventually.of_forall (fun _ => rfl)) _ _ hbase.1 hbase.2.1 hbase.2.2]
    exact mul_pos (Real.exp_pos _) (hK _ _ hbase)
  rwa [sectionalCurvature_smul D' x v w (Real.sqrt_pos.mpr hc).ne'
    (Real.sqrt_pos.mpr hc).ne'] at hpos

theorem standardCapConformalExponent_germ_tip (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r : ℝ} (hr : 0 < r) {x : StandardCapSpace}
    (hx : radialArclength g₀ ‖x‖ < r / 2) :
    standardCapConformalExponent g₀ C q epsilon r =ᶠ[𝓝 x]
      fun _ => smoothProfile C q epsilon (g₀.cylindrical_end.radius + 4) := by
  have hcont : Continuous (fun y : StandardCapSpace => radialArclength g₀ ‖y‖) :=
    (radialArclength_contDiff g₀).continuous.comp continuous_norm
  filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hx)] with y hy
  rw [standardCapConformalExponent_eq_profile]
  exact standardCapConformalProfile_eq_tip g₀ C q epsilon hr hy.le

theorem standardCap_sectional_multiplier_tip (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r : ℝ} (hr : 0 < r)
    (D : LeviCivitaData (positiveScaling g₀.metric
      (radialConformalMultiplier g₀ C q epsilon r)
      (radialConformalMultiplier_contDiff g₀ C q epsilon hr).contMDiff
      (radialConformalMultiplier_pos g₀ C q epsilon r)))
    {x : StandardCapSpace} (hx : radialArclength g₀ ‖x‖ < r / 2)
    (v w : StandardCapSpace)
    (hvv : g₀.metric.inner x v v = 1) (hww : g₀.metric.inner x w w = 1)
    (hvw : g₀.metric.inner x v w = 0) :
    D.sectionalCurvature x v w =
      Real.exp (2 * smoothProfile C q epsilon (g₀.cylindrical_end.radius + 4)) *
        g₀.connection.sectionalCurvature x v w := by
  let F := standardCapConformalExponent g₀ C q epsilon r
  have hFs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F :=
    (standardCapConformalExponent_contDiff g₀ C q epsilon hr).contMDiff
  have hmetric : positiveScaling g₀.metric (radialConformalMultiplier g₀ C q epsilon r)
      (radialConformalMultiplier_contDiff g₀ C q epsilon hr).contMDiff
      (radialConformalMultiplier_pos g₀ C q epsilon r) =
      positiveScaling g₀.metric (fun y => Real.exp (-2 * F y))
        (contMDiff_exp_neg_two hFs) (fun _ => Real.exp_pos _) := by
    have he : (fun y => Real.exp (-2 * F y)) = radialConformalMultiplier g₀ C q epsilon r :=
      funext (standardCapConformalExponent_exp g₀ C q epsilon r)
    congr 1
    exact he.symm
  revert D
  rw [hmetric]
  intro D
  have hF := standardCapConformalExponent_germ_tip g₀ C q epsilon hr hx
  rw [sectionalCurvature_positiveScaling_constant_germ g₀.metric g₀.connection F hFs D
    hF v w hvv hww hvw]
  change Real.exp (2 * standardCapConformalExponent g₀ C q epsilon r x) *
    g₀.connection.sectionalCurvature x v w = _
  rw [hF.eq_of_nhds]

theorem standardCap_angular_ratio_continuousAt (g₀ : StandardInitialMetric)
    {u : ℝ} (hu : 0 < u) :
    ContinuousAt (fun v => angularRadiusSlope g₀ v / euclideanWarpRadius g₀ v) u :=
  (angularRadiusSlope_contDiff g₀).continuous.continuousAt.div
    (euclideanWarpRadius_contDiff g₀).continuous.continuousAt
    (euclideanWarpRadius_pos g₀ hu).ne'

theorem standardCap_angular_ratio_le (g₀ : StandardInitialMetric)
    {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    angularRadiusSlope g₀ u / euclideanWarpRadius g₀ u ≤
      1 / euclideanWarpRadius g₀ a := by
  have hu : 0 < u := ha.trans_le hau
  have hp := euclideanWarpRadius_monotoneOn g₀ ha.le hu.le hau
  exact (div_le_div_of_nonneg_right (angularRadiusSlope_lt_one g₀ hu).le
    (euclideanWarpRadius_pos g₀ hu).le).trans
    (div_le_div_of_nonneg_left (by norm_num) (euclideanWarpRadius_pos g₀ ha) hp)

theorem standardCap_sectional_radial_nonneg (g₀ : StandardInitialMetric)
    {u : ℝ} (hu : 0 < u) :
    0 ≤ g₀.connection.sectionalCurvature (axisPoint u) (axisBasis 0) (axisBasis 1) := by
  rw [standardCap_sectional_radial_slope g₀ hu]
  exact div_nonneg (neg_nonneg.mpr (angularRadiusSlope_deriv_nonpos g₀ hu))
    (mul_pos (radialSpeed_pos g₀ u) (euclideanWarpRadius_pos g₀ hu)).le

theorem standardCap_sectional_tangential_continuousAt (g₀ : StandardInitialMetric)
    {u : ℝ} (hu : 0 < u) :
    ContinuousAt (fun v => g₀.connection.sectionalCurvature (axisPoint v)
      (axisBasis 1) (axisBasis 2)) u := by
  have ha := (axisRadialCoefficient_contDiff g₀).continuous.continuousAt (x := u)
  have hc := (axisTangentialCoefficient_contDiff g₀).continuous.continuousAt (x := u)
  have hc' := ((contDiff_infty_iff_deriv.mp
    (axisTangentialCoefficient_contDiff g₀)).2).continuous.continuousAt (x := u)
  have ha0 := axisRadialCoefficient_pos g₀ u
  have hc0 := axisTangentialCoefficient_pos g₀ u
  have hf : ContinuousAt (fun v : ℝ =>
      (4 * axisRadialCoefficient g₀ v * axisTangentialCoefficient g₀ v -
        (2 * axisTangentialCoefficient g₀ v +
          v * deriv (axisTangentialCoefficient g₀) v) ^ 2) /
      (4 * axisRadialCoefficient g₀ v * v ^ 2 * (axisTangentialCoefficient g₀ v) ^ 2)) u :=
    (((continuousAt_const.mul ha).mul hc).sub
      (((continuousAt_const.mul hc).add (continuousAt_id.mul hc')).pow 2)).div
      (((continuousAt_const.mul ha).mul (continuousAt_id.pow 2)).mul (hc.pow 2))
      (by positivity)
  apply hf.congr
  filter_upwards [lt_mem_nhds hu] with v hv
  exact (standardCap_sectional_tangential g₀ hv).symm

theorem standardCap_radial_endpoint_outer_pos (g₀ : StandardInitialMetric)
    {C q epsilon r u : ℝ} (hC : 0 < C) (hq : 0 < q) (hepsilon : 0 < epsilon)
    (hr : 0 < r) (hu : 0 < u) (ht : 3 * r / 4 < radialArclength g₀ u)
    (hs : 0 < g₀.cylindrical_end.radius + 4 - radialArclength g₀ u)
    (hbound : (g₀.cylindrical_end.radius + 4 - radialArclength g₀ u) ^ 2 *
      (angularRadiusSlope g₀ u / euclideanWarpRadius g₀ u) +
      2 * (g₀.cylindrical_end.radius + 4 - radialArclength g₀ u) < q) :
    0 < g₀.connection.sectionalCurvature (axisPoint u) (axisBasis 0) (axisBasis 1) +
      deriv (deriv (standardCapConformalProfile g₀ C q epsilon r)) (radialArclength g₀ u) +
      deriv (standardCapConformalProfile g₀ C q epsilon r) (radialArclength g₀ u) *
        (angularRadiusSlope g₀ u / euclideanWarpRadius g₀ u) := by
  let s := g₀.cylindrical_end.radius + 4 - radialArclength g₀ u
  let z := angularRadiusSlope g₀ u / euclideanWarpRadius g₀ u
  have hs0 : 0 < s := hs
  have hqz : s ^ 2 * z + 2 * s < q := hbound
  have hd : 0 < deriv (smoothProfile C q epsilon) s := by
    rw [smoothProfile_deriv hq]
    exact mul_pos (div_pos hq (sq_pos_of_pos hs0)) (smoothProfile_pos hC hq hepsilon hs0)
  have hb : 0 < (q - (s ^ 2 * z + 2 * s)) / s ^ 2 :=
    div_pos (sub_pos.mpr hqz) (sq_pos_of_pos hs0)
  have hid : deriv (deriv (smoothProfile C q epsilon)) s -
      deriv (smoothProfile C q epsilon) s * z =
      deriv (smoothProfile C q epsilon) s * ((q - (s ^ 2 * z + 2 * s)) / s ^ 2) := by
    rw [smoothProfile_second_deriv hq, smoothProfile_deriv hq]
    field_simp [hs0.ne']
    ring
  rw [standardCapConformalProfile_second_deriv_outer g₀ C q epsilon hr ht,
    standardCapConformalProfile_deriv_outer g₀ C q epsilon hr ht]
  change 0 < g₀.connection.sectionalCurvature (axisPoint u) (axisBasis 0) (axisBasis 1) +
    deriv (deriv (smoothProfile C q epsilon)) s + (-deriv (smoothProfile C q epsilon) s) * z
  rw [neg_mul, ← sub_eq_add_neg, add_sub_assoc, hid]
  exact add_pos_of_nonneg_of_pos (standardCap_sectional_radial_nonneg g₀ hu) (mul_pos hd hb)

theorem standardCap_radial_tip_endpoint_eventually_pos (g₀ : StandardInitialMetric)
    (C q r : ℝ) {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) :
    ∀ᶠ epsilon in 𝓝 (0 : ℝ), ∀ u ∈ K,
      0 < (1 / 4 : ℝ) +
        deriv (deriv (standardCapConformalProfile g₀ C q epsilon r)) (radialArclength g₀ u) +
        deriv (standardCapConformalProfile g₀ C q epsilon r) (radialArclength g₀ u) *
          (angularRadiusSlope g₀ u / euclideanWarpRadius g₀ u) := by
  have ht : Continuous (fun p : ℝ × ℝ => (p.1, radialArclength g₀ p.2)) :=
    continuous_fst.prodMk ((radialArclength_contDiff g₀).continuous.comp continuous_snd)
  have hd : Continuous (fun p : ℝ × ℝ =>
      deriv (standardCapConformalProfile g₀ C q p.1 r) (radialArclength g₀ p.2)) :=
    (standardCapConformalProfile_deriv_joint_contDiff g₀ C q r).continuous.comp ht
  have hdd : Continuous (fun p : ℝ × ℝ =>
      deriv (deriv (standardCapConformalProfile g₀ C q p.1 r)) (radialArclength g₀ p.2)) :=
    (standardCapConformalProfile_second_deriv_joint_contDiff g₀ C q r).continuous.comp ht
  apply hK.eventually_forall_of_forall_eventually
  intro u hu
  have hz : ContinuousAt (fun p : ℝ × ℝ =>
      angularRadiusSlope g₀ p.2 / euclideanWarpRadius g₀ p.2) (0, u) :=
    ContinuousAt.comp (f := fun p : ℝ × ℝ => p.2)
      (g := fun v : ℝ => angularRadiusSlope g₀ v / euclideanWarpRadius g₀ v)
      (x := (0, u)) (standardCap_angular_ratio_continuousAt g₀ (u := u) (hKpos hu))
      continuousAt_snd
  have he := (hdd.continuousAt.const_add (1 / 4 : ℝ)).add (hd.continuousAt.mul hz)
  apply he.eventually
  apply lt_mem_nhds
  change 0 < (1 / 4 : ℝ) +
    deriv (deriv (standardCapConformalProfile g₀ C q 0 r)) (radialArclength g₀ u) +
    deriv (standardCapConformalProfile g₀ C q 0 r) (radialArclength g₀ u) *
      (angularRadiusSlope g₀ u / euclideanWarpRadius g₀ u)
  simp only [standardCapConformalProfile_second_deriv_zero,
    standardCapConformalProfile_deriv_zero, zero_mul, add_zero]
  norm_num

theorem standardCap_tangential_endpoint_eventually_pos (g₀ : StandardInitialMetric)
    (C q r : ℝ) {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) :
    ∀ᶠ epsilon in 𝓝 (0 : ℝ), ∀ u ∈ K,
      0 < g₀.connection.sectionalCurvature (axisPoint u) (axisBasis 1) (axisBasis 2) +
        2 * deriv (standardCapConformalProfile g₀ C q epsilon r) (radialArclength g₀ u) *
          (angularRadiusSlope g₀ u / euclideanWarpRadius g₀ u) -
        (deriv (standardCapConformalProfile g₀ C q epsilon r) (radialArclength g₀ u)) ^ 2 := by
  have ht : Continuous (fun p : ℝ × ℝ => (p.1, radialArclength g₀ p.2)) :=
    continuous_fst.prodMk ((radialArclength_contDiff g₀).continuous.comp continuous_snd)
  have hd : Continuous (fun p : ℝ × ℝ =>
      deriv (standardCapConformalProfile g₀ C q p.1 r) (radialArclength g₀ p.2)) :=
    (standardCapConformalProfile_deriv_joint_contDiff g₀ C q r).continuous.comp ht
  apply hK.eventually_forall_of_forall_eventually
  intro u hu
  have hz : ContinuousAt (fun p : ℝ × ℝ =>
      angularRadiusSlope g₀ p.2 / euclideanWarpRadius g₀ p.2) (0, u) :=
    ContinuousAt.comp (f := fun p : ℝ × ℝ => p.2)
      (g := fun v : ℝ => angularRadiusSlope g₀ v / euclideanWarpRadius g₀ v)
      (x := (0, u)) (standardCap_angular_ratio_continuousAt g₀ (u := u) (hKpos hu))
      continuousAt_snd
  have hk : ContinuousAt (fun p : ℝ × ℝ => g₀.connection.sectionalCurvature
      (axisPoint p.2) (axisBasis 1) (axisBasis 2)) (0, u) :=
    ContinuousAt.comp (f := fun p : ℝ × ℝ => p.2)
      (g := fun v : ℝ => g₀.connection.sectionalCurvature (axisPoint v)
        (axisBasis 1) (axisBasis 2)) (x := (0, u))
      (standardCap_sectional_tangential_continuousAt g₀ (u := u) (hKpos hu)) continuousAt_snd
  have he := (hk.add ((hd.continuousAt.const_mul 2).mul hz)).sub
    (hd.continuousAt.pow 2)
  apply he.eventually
  apply lt_mem_nhds
  change 0 < g₀.connection.sectionalCurvature (axisPoint u) (axisBasis 1) (axisBasis 2) +
    2 * deriv (standardCapConformalProfile g₀ C q 0 r) (radialArclength g₀ u) *
      (angularRadiusSlope g₀ u / euclideanWarpRadius g₀ u) -
    (deriv (standardCapConformalProfile g₀ C q 0 r) (radialArclength g₀ u)) ^ 2
  simpa only [standardCapConformalProfile_deriv_zero, mul_zero, zero_mul, zero_pow
    (by norm_num : 2 ≠ 0), add_zero, sub_zero] using
    standardCap_sectional_tangential_pos g₀ (hKpos hu)

private theorem cap_axis_orthonormal (g₀ : StandardInitialMetric) (u : ℝ) :
    LeviCivitaData.IsOrthonormalPair g₀.metric (axisPoint u)
      ((radialSpeed g₀ u)⁻¹ • axisBasis 0)
      ((Real.sqrt (axisTangentialCoefficient g₀ u))⁻¹ • axisBasis 1) := by
  have ha : (radialSpeed g₀ u) ^ 2 = axisRadialCoefficient g₀ u :=
    Real.sq_sqrt (axisRadialCoefficient_pos g₀ u).le
  have hc := Real.sq_sqrt (axisTangentialCoefficient_pos g₀ u).le
  have ha0 := (radialSpeed_pos g₀ u).ne'
  have hc0 := (Real.sqrt_pos.mpr (axisTangentialCoefficient_pos g₀ u)).ne'
  unfold LeviCivitaData.IsOrthonormalPair
  simp only [map_smul, smul_apply, smul_eq_mul, axis_metric_zero_one, mul_zero]
  change (radialSpeed g₀ u)⁻¹ * ((radialSpeed g₀ u)⁻¹ * axisRadialCoefficient g₀ u) = 1 ∧
    (Real.sqrt (axisTangentialCoefficient g₀ u))⁻¹ *
      ((Real.sqrt (axisTangentialCoefficient g₀ u))⁻¹ * axisTangentialCoefficient g₀ u) = 1 ∧ True
  refine ⟨?_, ?_, trivial⟩
  · rw [← ha]
    field_simp
  · generalize hs : Real.sqrt (axisTangentialCoefficient g₀ u) = s at *
    rw [← hc]
    field_simp

private theorem cap_axis_sectional_eq_tip (g₀ : StandardInitialMetric)
    {R : ℝ} (hR : 0 < R)
    (htip : ∀ x ∈ g₀.metric.ball 0 R, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g₀.metric x v w →
        g₀.connection.sectionalCurvature x v w = (1 / 4 : ℝ))
    {u : ℝ} (hu : 0 < u) (huR : radialArclength g₀ u < R) :
    g₀.connection.sectionalCurvature (axisPoint u) (axisBasis 0) (axisBasis 1) =
      (1 / 4 : ℝ) := by
  have hnorm : ‖axisPoint u‖ = u := by
    rw [axisPoint_eq_smul]
    simp [axisBasis, norm_smul, abs_of_pos hu]
  have hin : axisPoint u ∈ g₀.metric.ball 0 R := by
    change g₀.metric.edist 0 (axisPoint u) < ENNReal.ofReal R
    rw [standard_edist_zero, hnorm]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr huR
  have hk := htip (axisPoint u) hin _ _ (cap_axis_orthonormal g₀ u)
  rw [sectionalCurvature_smul g₀.connection _ _ _
    (inv_ne_zero (radialSpeed_pos g₀ u).ne')
    (inv_ne_zero (Real.sqrt_pos.mpr (axisTangentialCoefficient_pos g₀ u)).ne')] at hk
  exact hk

theorem exists_standardCap_multiplier_positive (g₀ : StandardInitialMetric) :
    ∃ (r : ℝ) (hr : 0 < r), r ≤ g₀.cylindrical_end.radius ∧
      ∃ q0 : ℝ, 100 * (g₀.cylindrical_end.radius + 4) ^ 2 < q0 ∧
        ∀ q : ℝ, q0 ≤ q → ∀ C : ℝ, 0 < C → ∃ delta : ℝ, 0 < delta ∧
          ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
          ∀ (D : LeviCivitaData (positiveScaling g₀.metric
            (radialConformalMultiplier g₀ C q epsilon r)
            (radialConformalMultiplier_contDiff g₀ C q epsilon hr).contMDiff
            (radialConformalMultiplier_pos g₀ C q epsilon r))) (x : StandardCapSpace),
          radialArclength g₀ ‖x‖ ≤ g₀.cylindrical_end.radius + 3 →
          ∀ v w : StandardCapSpace,
          LeviCivitaData.IsOrthonormalPair (positiveScaling g₀.metric
            (radialConformalMultiplier g₀ C q epsilon r)
            (radialConformalMultiplier_contDiff g₀ C q epsilon hr).contMDiff
            (radialConformalMultiplier_pos g₀ C q epsilon r)) x v w →
          0 < D.sectionalCurvature x v w := by
  obtain ⟨Rtip, hRtip, htip⟩ := g₀.tip_sectional_curvature
  let r := min g₀.cylindrical_end.radius Rtip / 2
  have hr : 0 < r := half_pos (lt_min g₀.cylindrical_end.radius_pos hRtip)
  have hrA : r ≤ g₀.cylindrical_end.radius := by
    dsimp only [r]
    linarith only [min_le_left g₀.cylindrical_end.radius Rtip,
      g₀.cylindrical_end.radius_pos]
  have hrR : r < Rtip := by
    dsimp only [r]
    linarith only [min_le_right g₀.cylindrical_end.radius Rtip, hRtip]
  let A := g₀.cylindrical_end.radius + 4
  let uL := radialEuclideanRadius g₀ (r / 2)
  let uT := radialEuclideanRadius g₀ r
  let uU := radialEuclideanRadius g₀ (g₀.cylindrical_end.radius + 3)
  have huL : 0 < uL := (radialEuclideanRadius_pos_iff g₀ _).mpr (half_pos hr)
  have huT : 0 < uT := (radialEuclideanRadius_pos_iff g₀ _).mpr hr
  let pT := euclideanWarpRadius g₀ uT
  have hpT : 0 < pT := euclideanWarpRadius_pos g₀ huT
  let q0 := max (100 * A ^ 2) (A ^ 2 / pT + 2 * A) + 1
  have hq0 : 100 * A ^ 2 < q0 := by
    dsimp only [q0]
    linarith only [le_max_left (100 * A ^ 2) (A ^ 2 / pT + 2 * A)]
  refine ⟨r, hr, hrA, q0, hq0, ?_⟩
  intro q hq C hC
  have hqpos : 0 < q := lt_of_le_of_lt (by positivity) (hq0.trans_le hq)
  have hqgeom : A ^ 2 / pT + 2 * A < q := by
    have h := le_max_right (100 * A ^ 2) (A ^ 2 / pT + 2 * A)
    dsimp only [q0] at hq
    linarith only [h, hq]
  have hKpos (b : ℝ) : Icc uL b ⊆ Ioi 0 := fun _ hu => huL.trans_le hu.1
  have hrad := standardCap_radial_tip_endpoint_eventually_pos g₀ C q r
    (K := Icc uL uT) isCompact_Icc (hKpos uT)
  have htan := standardCap_tangential_endpoint_eventually_pos g₀ C q r
    (K := Icc uL uU) isCompact_Icc (hKpos uU)
  obtain ⟨d, hd, hsmall⟩ := Metric.eventually_nhds_iff.mp (hrad.and htan)
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro epsilon hepsilon heps D x hx v w hpair
  have heps' : dist epsilon 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hepsilon]
    linarith only [heps, hd]
  obtain ⟨hR, hT⟩ := hsmall heps'
  by_cases hinner : radialArclength g₀ ‖x‖ < r / 2
  · have hin : x ∈ g₀.metric.ball 0 Rtip := by
      change g₀.metric.edist 0 x < ENNReal.ofReal Rtip
      rw [standard_edist_zero]
      exact (ENNReal.ofReal_lt_ofReal_iff hRtip).mpr (by linarith only [hinner, hrR, hr])
    let m := radialConformalMultiplier g₀ C q epsilon r
    have hbase := positiveScaling_orthonormal_sqrt g₀.metric m
      (radialConformalMultiplier_contDiff g₀ C q epsilon hr).contMDiff
      (radialConformalMultiplier_pos g₀ C q epsilon r) x v w hpair
    have hk := htip x hin _ _ hbase
    have hhom := standardCap_sectional_multiplier_tip g₀ C q epsilon hr D hinner
      (Real.sqrt (m x) • v) (Real.sqrt (m x) • w) hbase.1 hbase.2.1 hbase.2.2
    have hms : Real.sqrt (m x) ≠ 0 :=
      (Real.sqrt_pos.mpr (radialConformalMultiplier_pos g₀ C q epsilon r x)).ne'
    rw [sectionalCurvature_smul D x v w hms hms, hk] at hhom
    rw [hhom]
    exact mul_pos (Real.exp_pos _) (by norm_num)
  have hlow : uL ≤ ‖x‖ := by
    simpa only [uL, radialEuclideanRadius_arclength] using
      (radialEuclideanRadius_strictMono g₀).monotone (le_of_not_gt hinner)
  have hupper : ‖x‖ ≤ uU := by
    simpa only [uU, radialEuclideanRadius_arclength] using
      (radialEuclideanRadius_strictMono g₀).monotone hx
  have hu : 0 < ‖x‖ := huL.trans_le hlow
  apply standardCap_sectional_multiplier_pos g₀ C q epsilon hr D (norm_pos_iff.mp hu)
    ?_ (hT ‖x‖ ⟨hlow, hupper⟩) v w hpair
  by_cases htipregion : radialArclength g₀ ‖x‖ ≤ r
  · rw [cap_axis_sectional_eq_tip g₀ hRtip htip hu (htipregion.trans_lt hrR)]
    apply hR ‖x‖
    refine ⟨hlow, ?_⟩
    simpa only [uT, radialEuclideanRadius_arclength] using
      (radialEuclideanRadius_strictMono g₀).monotone htipregion
  have houter : r < radialArclength g₀ ‖x‖ := lt_of_not_ge htipregion
  have hule : uT ≤ ‖x‖ := by
    simpa only [uT, radialEuclideanRadius_arclength] using
      (radialEuclideanRadius_strictMono g₀).monotone houter.le
  let s := A - radialArclength g₀ ‖x‖
  have hs : 0 < s := by dsimp only [s, A]; linarith only [hx]
  have hsA : s ≤ A := sub_le_self _ (radialArclength_pos g₀ hu).le
  have hsquare : s ^ 2 ≤ A ^ 2 := sq_le_sq₀ hs.le (hs.le.trans hsA) |>.mpr hsA
  have hz := standardCap_angular_ratio_le g₀ huT hule
  have hgeom : s ^ 2 * (angularRadiusSlope g₀ ‖x‖ / euclideanWarpRadius g₀ ‖x‖) +
      2 * s < q := by
    calc
      _ ≤ s ^ 2 * (1 / pT) + 2 * s :=
        add_le_add (mul_le_mul_of_nonneg_left hz (sq_nonneg s)) le_rfl
      _ ≤ A ^ 2 / pT + 2 * A := by
        rw [mul_one_div]
        exact add_le_add (div_le_div_of_nonneg_right hsquare hpT.le)
          (mul_le_mul_of_nonneg_left hsA (by norm_num))
      _ < q := hqgeom
  exact standardCap_radial_endpoint_outer_pos g₀ hC hqpos hepsilon hr hu
    (by linarith only [hr, houter]) hs hgeom

end PoincareConjecture.M36
