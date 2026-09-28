import PoincareConjecture.Proofs.M36.StandardCapMultiplier
import PoincareConjecture.Proofs.M36.SurgeryMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Proofs.M03.ConnectionExistence











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u v

namespace PoincareConjecture.M36



theorem sectionalCurvature_eq_of_local_isometry
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
    [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]
    {g : RiemannianMetric 3 X} {h : RiemannianMetric 3 Y}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 3) y,
      g.inner y a b = h.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b))
    {x : X} (hx : x ∈ U) (a b : TangentSpace (𝓡 3) x) :
    D.sectionalCurvature x a b = D'.sectionalCurvature (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x a) (mfderiv (𝓡 3) (𝓡 3) f x b) := by
  unfold LeviCivitaData.sectionalCurvature
  rw [D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx,
    hmetric x hx a a, hmetric x hx b b, hmetric x hx a b]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem surgeryMetric_inner_pureCap (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : (7 / 4 : ℝ) ≤ standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y))
    (a b : TangentSpace (𝓡 3) y) :
    (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner y a b =
      (positiveScaling (positiveScaling g₀.metric
        (radialConformalMultiplier g₀ C q N.epsilon r)
        (radialConformalMultiplier_contDiff g₀ C q N.epsilon hr).contMDiff
        (radialConformalMultiplier_pos g₀ C q N.epsilon r))
        (fun _ => eta / N.connection.scalarCurvature N.center) contMDiff_const
        (fun _ => div_pos heta hlambda)).inner (surgeryBallInclusion g₀ _ y)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ _) y a)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryBallInclusion g₀ _) y b) := by
  have ha : surgeryNeckWeight g₀ N y = 0 := neckCutoff_eq_zero hy
  rw [surgeryMetric_inner, ha]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  change radialConformalMultiplier g₀ C q N.epsilon r (surgeryBallInclusion g₀ _ y) *
    (eta / N.connection.scalarCurvature N.center *
      metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y a b) =
    eta / N.connection.scalarCurvature N.center *
      (radialConformalMultiplier g₀ C q N.epsilon r (surgeryBallInclusion g₀ _ y) *
        metricPullbackForm g₀.metric (surgeryBallInclusion g₀ _) y a b)
  ring




theorem surgeryMetric_sectional_pureCap_pos (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    (Dcap : LeviCivitaData (positiveScaling g₀.metric
      (radialConformalMultiplier g₀ C q N.epsilon r)
      (radialConformalMultiplier_contDiff g₀ C q N.epsilon hr).contMDiff
      (radialConformalMultiplier_pos g₀ C q N.epsilon r)))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : (7 / 4 : ℝ) < standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y))
    (hcap : ∀ a b : StandardCapSpace,
      LeviCivitaData.IsOrthonormalPair (positiveScaling g₀.metric
        (radialConformalMultiplier g₀ C q N.epsilon r)
        (radialConformalMultiplier_contDiff g₀ C q N.epsilon hr).contMDiff
        (radialConformalMultiplier_pos g₀ C q N.epsilon r))
        (surgeryBallInclusion g₀ _ y) a b →
      0 < Dcap.sectionalCurvature (surgeryBallInclusion g₀ _ y) a b)
    (a b : TangentSpace (𝓡 3) y)
    (hpair : LeviCivitaData.IsOrthonormalPair
      (surgeryMetric g₀ N hcut C q eta r hlambda heta hr) y a b) :
    0 < D.sectionalCurvature y a b := by
  let cap := positiveScaling g₀.metric (radialConformalMultiplier g₀ C q N.epsilon r)
    (radialConformalMultiplier_contDiff g₀ C q N.epsilon hr).contMDiff
    (radialConformalMultiplier_pos g₀ C q N.epsilon r)
  let c := eta / N.connection.scalarCurvature N.center
  have hc : 0 < c := div_pos heta hlambda
  let physicalCap := positiveScaling cap (fun _ => c) contMDiff_const (fun _ => hc)
  obtain ⟨Dphysical⟩ := exists_leviCivitaData physicalCap
  let i := surgeryBallInclusion.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)
  let U : Set (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :=
    {z | (7 / 4 : ℝ) < standardSurgeryHeight g₀ (i z)}
  have hU : IsOpen U := isOpen_lt continuous_const
    ((standardSurgeryHeight_continuous g₀).comp
      (surgeryBallInclusion_contMDiff g₀ _).continuous)
  have hmetric : ∀ z ∈ U, ∀ v w : TangentSpace (𝓡 3) z,
      (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner z v w =
        physicalCap.inner (i z)
          (mfderiv (𝓡 3) (𝓡 3) i z v) (mfderiv (𝓡 3) (𝓡 3) i z w) := by
    intro z hz v w
    exact surgeryMetric_inner_pureCap g₀ N hcut C q eta r hlambda heta hr hz.le v w
  have hpair' : LeviCivitaData.IsOrthonormalPair physicalCap (i y)
      (mfderiv (𝓡 3) (𝓡 3) i y a) (mfderiv (𝓡 3) (𝓡 3) i y b) := by
    unfold LeviCivitaData.IsOrthonormalPair at hpair ⊢
    rw [← hmetric y hy a a, ← hmetric y hy b b, ← hmetric y hy a b]
    exact hpair
  rw [sectionalCurvature_eq_of_local_isometry D Dphysical hU
    (surgeryBallInclusion_contMDiff g₀ _).contMDiffOn hmetric hy]
  exact positiveScaling_const_sectional_pos Dcap hc Dphysical (i y) hcap _ _ hpair'





theorem exists_surgeryMetric_pureCap_positive (g₀ : StandardInitialMetric) :
    ∃ (r : ℝ) (hr : 0 < r), r ≤ g₀.cylindrical_end.radius ∧
      ∃ q0 : ℝ, 100 * (g₀.cylindrical_end.radius + 4) ^ 2 < q0 ∧
        ∀ q : ℝ, q0 ≤ q → ∀ C : ℝ, 0 < C → ∃ delta : ℝ, 0 < delta ∧
          ∀ (M : Type u) [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
            (g : RiemannianMetric 3 M) (N : EpsilonNeck g)
            (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (eta : ℝ)
            (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta),
          N.epsilon ≤ delta →
          ∀ (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
            (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)),
          radialArclength g₀ ‖surgeryBallInclusion g₀ _ y‖ ≤
            g₀.cylindrical_end.radius + 2 →
          ∀ a b : TangentSpace (𝓡 3) y,
          LeviCivitaData.IsOrthonormalPair
            (surgeryMetric g₀ N hcut C q eta r hlambda heta hr) y a b →
          0 < D.sectionalCurvature y a b := by
  obtain ⟨r, hr, hrA, q0, hq0, hmodel⟩ := exists_standardCap_multiplier_positive g₀
  refine ⟨r, hr, hrA, q0, hq0, ?_⟩
  intro q hq C hC
  obtain ⟨delta, hdelta, hpositive⟩ := hmodel q hq C hC
  refine ⟨delta, hdelta, ?_⟩
  intro M _ _ _ g N hcut eta hlambda heta hepsilon D y hy a b hpair
  obtain ⟨Dcap⟩ := exists_leviCivitaData (positiveScaling g₀.metric
    (radialConformalMultiplier g₀ C q N.epsilon r)
    (radialConformalMultiplier_contDiff g₀ C q N.epsilon hr).contMDiff
    (radialConformalMultiplier_pos g₀ C q N.epsilon r))
  have hheight : (7 / 4 : ℝ) <
      standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) := by
    unfold standardSurgeryHeight
    linarith only [hy]
  exact surgeryMetric_sectional_pureCap_pos g₀ N hcut C q eta r hlambda heta hr D Dcap
    hheight (hpositive N.epsilon N.epsilon_pos hepsilon Dcap _ (by linarith only [hy]))
    a b hpair

section Profile

variable {n : ℕ} {X : Type v} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
  {h : RiemannianMetric n X}

omit [IsManifold (𝓡 n) ∞ X] in

theorem mvfderiv_scalar_profile_germ {F s : X → ℝ} {phi : ℝ → ℝ} {x : X}
    (hphi : DifferentiableAt ℝ phi (s x))
    (hs : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) (a : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) F x a = deriv phi (s x) * mvfderiv (𝓡 n) s x a := by
  have hd : mvfderiv (𝓡 n) F x = mvfderiv (𝓡 n) (phi ∘ s) x := heq.mfderiv_eq
  rw [hd, mvfderiv_comp_apply x hphi.mdifferentiableAt hs a]
  simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
  exact fderiv_eq_deriv_mul (𝕜 := ℝ)


theorem gradient_scalar_profile_germ (D : LeviCivitaData h)
    {F s : X → ℝ} {phi : ℝ → ℝ} {x : X}
    (hphi : DifferentiableAt ℝ phi (s x))
    (hs : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) :
    D.gradient F x = deriv phi (s x) • D.gradient s x := by
  apply (h.inner_isInvertible x).injective
  ext a
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]
  exact mvfderiv_scalar_profile_germ hphi hs heq a




theorem hessian_scalar_profile_germ (D : LeviCivitaData h)
    {F s : X → ℝ} {phi : ℝ → ℝ} {x : X}
    (hphi : ContDiff ℝ ∞ phi) (hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) (a b : TangentSpace (𝓡 n) x) :
    D.hessian F x a b = deriv phi (s x) * D.hessian s x a b +
      deriv (deriv phi) (s x) * mvfderiv (𝓡 n) s x a * mvfderiv (𝓡 n) s x b := by
  have hphi' : ContDiff ℝ ∞ (deriv phi) := (contDiff_infty_iff_deriv.mp hphi).2
  have hsd := hs.mdifferentiableAt (by simp)
  have hFs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ F x :=
    (hphi.contMDiff.contMDiffAt.comp x hs).congr_of_eventuallyEq heq
  let c : X → ℝ := fun y => deriv phi (s y)
  have hc : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ c x :=
    hphi'.contMDiff.contMDiffAt.comp x hs
  have hs1 := (contMDiffAt_iff_contMDiffAt_nhds
    (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      (hs.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞))
  have hgrad : D.gradient F =ᶠ[nhds x] c • D.gradient s := by
    filter_upwards [hs1, heq.eventually_nhds] with y hsy heqy
    exact gradient_scalar_profile_germ D (hphi.differentiable (by simp) (s y))
      (hsy.mdifferentiableAt (by simp)) heqy
  have hconn := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((D.contMDiffAt_gradient hFs).mdifferentiableAt (by simp))
    ((hc.smul_section (D.contMDiffAt_gradient hs)).mdifferentiableAt (by simp))
    (by simp) hgrad
  rw [D.hessian_eq_inner_connection_gradient hFs, hconn,
    D.connection.isCovariantDerivativeOnUniv.leibniz
      ((D.contMDiffAt_gradient hs).mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp))]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul]
  rw [← D.hessian_eq_inner_connection_gradient hs, D.inner_gradient,
    mvfderiv_scalar_profile_germ (F := c) (hphi'.differentiable (by simp) (s x)) hsd
      (Filter.EventuallyEq.rfl)]




theorem sectionalCurvature_positiveScaling_profile
    (h : RiemannianMetric n X) (D : LeviCivitaData h)
    (F : X → ℝ) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling h (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : X → ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : X)
    (hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) (a b : TangentSpace (𝓡 n) x)
    (haa : h.inner x a a = 1) (hbb : h.inner x b b = 1) (hab : h.inner x a b = 0) :
    D'.sectionalCurvature x a b = Real.exp (2 * phi (s x)) *
      (D.sectionalCurvature x a b +
        deriv phi (s x) * (D.hessian s x a a + D.hessian s x b b) +
        (deriv (deriv phi) (s x) + (deriv phi (s x)) ^ 2) *
          ((mvfderiv (𝓡 n) s x a) ^ 2 + (mvfderiv (𝓡 n) s x b) ^ 2) -
        (deriv phi (s x)) ^ 2 * h.inner x (D.gradient s x) (D.gradient s x)) := by
  have hpd := hphi.differentiable (by simp) (s x)
  have hsd := hs.mdifferentiableAt (by simp)
  rw [sectionalCurvature_positiveScaling_exp h D F hF D' x a b haa hbb hab,
    heq.self_of_nhds, hessian_scalar_profile_germ D hphi hs heq a a,
    hessian_scalar_profile_germ D hphi hs heq b b,
    mvfderiv_scalar_profile_germ hpd hsd heq a,
    mvfderiv_scalar_profile_germ hpd hsd heq b,
    gradient_scalar_profile_germ D hpd hsd heq]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring




theorem sectionalCurvature_positiveScaling_profile_lower_bound
    (h : RiemannianMetric n X) (D : LeviCivitaData h)
    (F : X → ℝ) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling h (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : X → ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : X)
    (hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) (a b : TangentSpace (𝓡 n) x)
    (haa : h.inner x a a = 1) (hbb : h.inner x b b = 1) (hab : h.inner x a b = 0)
    (B G : ℝ) (hp : 0 ≤ deriv phi (s x))
    (hHa : -B ≤ D.hessian s x a a) (hHb : -B ≤ D.hessian s x b b)
    (hG : h.inner x (D.gradient s x) (D.gradient s x) ≤ G) :
    Real.exp (2 * phi (s x)) *
      (D.sectionalCurvature x a b + deriv (deriv phi) (s x) *
        ((mvfderiv (𝓡 n) s x a) ^ 2 + (mvfderiv (𝓡 n) s x b) ^ 2) -
        2 * B * deriv phi (s x) - G * (deriv phi (s x)) ^ 2) ≤
      D'.sectionalCurvature x a b := by
  rw [sectionalCurvature_positiveScaling_profile h D F hF D' s phi hphi x hs heq
    a b haa hbb hab]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hH := mul_le_mul_of_nonneg_left (add_le_add hHa hHb) hp
  have hN := mul_le_mul_of_nonneg_left hG (sq_nonneg (deriv phi (s x)))
  have hA := mul_nonneg (sq_nonneg (deriv phi (s x)))
    (add_nonneg (sq_nonneg (mvfderiv (𝓡 n) s x a)) (sq_nonneg (mvfderiv (𝓡 n) s x b)))
  nlinarith only [hH, hN, hA]




theorem sectionalCurvature_positiveScaling_profile_lower_of_split
    (h : RiemannianMetric n X) (D : LeviCivitaData h)
    (F : X → ℝ) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling h (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : X → ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : X)
    (hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) (a b : TangentSpace (𝓡 n) x)
    (haa : h.inner x a a = 1) (hbb : h.inner x b b = 1) (hab : h.inner x a b = 0)
    (B kappa xi : ℝ) (hp : 0 ≤ deriv phi (s x)) (ht : 0 ≤ deriv (deriv phi) (s x))
    (hHa : -B ≤ D.hessian s x a a) (hHb : -B ≤ D.hessian s x b b)
    (hG : h.inner x (D.gradient s x) (D.gradient s x) ≤ 2)
    (herr : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 ≤
      deriv (deriv phi) (s x) / 4)
    (hgap : (mvfderiv (𝓡 n) s x a) ^ 2 + (mvfderiv (𝓡 n) s x b) ^ 2 < 1 / 2 →
      kappa ≤ D.sectionalCurvature x a b)
    (hsmall : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 ≤ kappa)
    (hxi : 0 ≤ xi) (hK : -xi ≤ D.sectionalCurvature x a b)
    (hamp : 2 * xi * phi (s x) ≤ deriv (deriv phi) (s x) / 4) :
    -xi ≤ D'.sectionalCurvature x a b := by
  let f := phi (s x)
  let p := deriv phi (s x)
  let t := deriv (deriv phi) (s x)
  let A := (mvfderiv (𝓡 n) s x a) ^ 2 + (mvfderiv (𝓡 n) s x b) ^ 2
  let K := D.sectionalCurvature x a b
  have hA0 : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hL := sectionalCurvature_positiveScaling_profile_lower_bound h D F hF D' s phi
    hphi x hs heq a b haa hbb hab B 2 hp hHa hHb hG
  change Real.exp (2 * f) * (K + t * A - 2 * B * p - 2 * p ^ 2) ≤
    D'.sectionalCurvature x a b at hL
  change 0 ≤ t at ht
  change 2 * B * p + 2 * p ^ 2 ≤ t / 4 at herr
  change 2 * B * p + 2 * p ^ 2 ≤ kappa at hsmall
  change 2 * xi * f ≤ t / 4 at hamp
  by_cases hA : 1 / 2 ≤ A
  · have hgain : K + t / 4 ≤ K + t * A - 2 * B * p - 2 * p ^ 2 := by
      have hta := mul_le_mul_of_nonneg_left hA ht
      nlinarith only [hta, herr]
    have hnegative := mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg (2 * f)) hxi
    have hcomp : -xi * Real.exp (-(2 * f)) ≤ -xi + t / 4 := by
      nlinarith only [hnegative, hamp]
    have hcancel : Real.exp (2 * f) * Real.exp (-(2 * f)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      -xi = -xi * (Real.exp (2 * f) * Real.exp (-(2 * f))) := by rw [hcancel, mul_one]
      _ = Real.exp (2 * f) * (-xi * Real.exp (-(2 * f))) := by ring
      _ ≤ Real.exp (2 * f) * (-xi + t / 4) :=
        mul_le_mul_of_nonneg_left hcomp (Real.exp_pos _).le
      _ ≤ Real.exp (2 * f) * (K + t / 4) :=
        mul_le_mul_of_nonneg_left (by dsimp [K]; linarith only [hK]) (Real.exp_pos _).le
      _ ≤ Real.exp (2 * f) * (K + t * A - 2 * B * p - 2 * p ^ 2) :=
        mul_le_mul_of_nonneg_left hgain (Real.exp_pos _).le
      _ ≤ D'.sectionalCurvature x a b := hL
  · have hbase : kappa ≤ K := hgap (lt_of_not_ge hA)
    have hbracket : 0 ≤ K + t * A - 2 * B * p - 2 * p ^ 2 := by
      nlinarith only [hbase, hsmall, mul_nonneg ht hA0]
    exact (neg_nonpos.mpr hxi).trans ((mul_nonneg (Real.exp_pos _).le hbracket).trans hL)



theorem sectionalCurvature_positiveScaling_profile_pos_of_split
    (h : RiemannianMetric n X) (D : LeviCivitaData h)
    (F : X → ℝ) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling h (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : X → ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : X)
    (hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) (a b : TangentSpace (𝓡 n) x)
    (haa : h.inner x a a = 1) (hbb : h.inner x b b = 1) (hab : h.inner x a b = 0)
    (B kappa : ℝ) (hp : 0 ≤ deriv phi (s x)) (ht : 0 ≤ deriv (deriv phi) (s x))
    (hHa : -B ≤ D.hessian s x a a) (hHb : -B ≤ D.hessian s x b b)
    (hG : h.inner x (D.gradient s x) (D.gradient s x) ≤ 2)
    (herr : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 ≤
      deriv (deriv phi) (s x) / 4)
    (hgap : (mvfderiv (𝓡 n) s x a) ^ 2 + (mvfderiv (𝓡 n) s x b) ^ 2 < 1 / 2 →
      kappa ≤ D.sectionalCurvature x a b)
    (hsmall : 2 * B * deriv phi (s x) + 2 * (deriv phi (s x)) ^ 2 < kappa)
    (hK : 0 < D.sectionalCurvature x a b) :
    0 < D'.sectionalCurvature x a b := by
  let p := deriv phi (s x)
  let t := deriv (deriv phi) (s x)
  let A := (mvfderiv (𝓡 n) s x a) ^ 2 + (mvfderiv (𝓡 n) s x b) ^ 2
  let K := D.sectionalCurvature x a b
  have hL := sectionalCurvature_positiveScaling_profile_lower_bound h D F hF D' s phi
    hphi x hs heq a b haa hbb hab B 2 hp hHa hHb hG
  change Real.exp (2 * phi (s x)) * (K + t * A - 2 * B * p - 2 * p ^ 2) ≤
    D'.sectionalCurvature x a b at hL
  change 0 ≤ t at ht
  change 0 < K at hK
  change 2 * B * p + 2 * p ^ 2 ≤ t / 4 at herr
  change 2 * B * p + 2 * p ^ 2 < kappa at hsmall
  have hbracket : 0 < K + t * A - 2 * B * p - 2 * p ^ 2 := by
    by_cases hA : 1 / 2 ≤ A
    · have hta := mul_le_mul_of_nonneg_left hA ht
      nlinarith only [hta, herr, hK, ht]
    · have hbase : kappa ≤ K := hgap (lt_of_not_ge hA)
      have hA0 : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
      nlinarith only [hbase, hsmall, mul_nonneg ht hA0]
  exact (mul_pos (Real.exp_pos _) hbracket).trans_le hL




theorem sectionalCurvature_positiveScaling_smoothProfile_retained
    (h : RiemannianMetric n X) (D : LeviCivitaData h)
    (F : X → ℝ) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling h (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : X → ℝ) (C epsilon : ℝ) {q : ℝ} (hq : 0 < q) (x : X)
    (hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => smoothProfile C q epsilon (s y)) (hx : s x ≤ 0)
    (a b : TangentSpace (𝓡 n) x)
    (haa : h.inner x a a = 1) (hbb : h.inner x b b = 1) (hab : h.inner x a b = 0) :
    D'.sectionalCurvature x a b = D.sectionalCurvature x a b := by
  have hz : smoothProfile C q epsilon (s x) = 0 := smoothProfile_eq_zero hq hx
  have hd : deriv (smoothProfile C q epsilon) (s x) = 0 := by
    rw [smoothProfile_deriv hq, hz, mul_zero]
  have hdd : deriv (deriv (smoothProfile C q epsilon)) (s x) = 0 := by
    rw [smoothProfile_second_deriv hq, hz, mul_zero]
  rw [sectionalCurvature_positiveScaling_profile h D F hF D' s
    (smoothProfile C q epsilon) (smoothProfile_contDiff C q epsilon) x hs heq a b haa hbb hab]
  simp only [hz, hd, hdd, mul_zero, Real.exp_zero, zero_mul, add_zero,
    zero_pow (by norm_num : 2 ≠ 0), sub_zero, one_mul]

end Profile



theorem standardCapConformalExponent_eq_on_transition (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r : ℝ} (hr : 0 < r) (hrA : r ≤ g₀.cylindrical_end.radius)
    {x : StandardCapSpace} (hx : standardSurgeryHeight g₀ x ≤ 2) :
    standardCapConformalExponent g₀ C q epsilon r x =
      smoothProfile C q epsilon (standardSurgeryHeight g₀ x) := by
  unfold standardCapConformalExponent
  rw [radialConformalMultiplier_eq_on_transition g₀ C q epsilon hr hrA hx]
  simp only [conformalFactor, Real.log_exp]
  ring




theorem surgeryMetric_sectional_retained (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 0)
    (a b : TangentSpace (𝓡 3) y)
    (hpair : LeviCivitaData.IsOrthonormalPair
      (surgeryMetric g₀ N hcut C q eta r hlambda heta hr) y a b) :
    D.sectionalCurvature y a b = N.connection.sectionalCurvature
      (surgeryRetainedInverse g₀ N y)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y a)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y b) := by
  let i := surgeryBallInclusion.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)
  let s := standardSurgeryHeight g₀ ∘ i
  let E := standardCapConformalExponent g₀ C q N.epsilon r ∘ i
  let H := surgeryMetric g₀ N hcut C q eta r hlambda heta hr
  have hE : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ E :=
    (standardCapConformalExponent_contDiff g₀ C q N.epsilon hr).contMDiff.comp
      (surgeryBallInclusion_contMDiff g₀ _)
  let J := positiveScaling H (fun z => Real.exp (-2 * (-E z)))
    (contMDiff_exp_neg_two hE.neg) (fun _ => Real.exp_pos _)
  obtain ⟨DJ⟩ := exists_leviCivitaData J
  let U : Set (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) := {z | s z < 1}
  have hU : IsOpen U := isOpen_lt
    ((standardSurgeryHeight_continuous g₀).comp
      (surgeryBallInclusion_contMDiff g₀ _).continuous) continuous_const
  have hyU : y ∈ U := lt_of_le_of_lt hy (by norm_num)
  have hne : ∀ z ∈ U, i z ≠ 0 := by
    intro z hz hzero
    change standardSurgeryHeight g₀ (i z) < 1 at hz
    rw [hzero, standardSurgeryHeight_zero] at hz
    linarith [g₀.cylindrical_end.radius_pos]
  have hcancel (z : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :
      Real.exp (-2 * (-E z)) * surgeryConformalMultiplier g₀ N C q r z = 1 := by
    change Real.exp (-2 * (-E z)) * radialConformalMultiplier g₀ C q N.epsilon r (i z) = 1
    rw [← standardCapConformalExponent_exp g₀ C q N.epsilon r (i z)]
    change Real.exp (-2 * (-E z)) * Real.exp (-2 * E z) = 1
    rw [← Real.exp_add, show -2 * (-E z) + -2 * E z = 0 by ring, Real.exp_zero]
  have hmetric : ∀ z ∈ U, ∀ v w : TangentSpace (𝓡 3) z,
      J.inner z v w = g.inner (surgeryRetainedInverse g₀ N z)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) z v)
        (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) z w) := by
    intro z hz v w
    change s z < 1 at hz
    have hweight : surgeryNeckWeight g₀ N z = 1 :=
      neckCutoff_eq_one (by change s z ≤ 5 / 4; linarith only [hz])
    change Real.exp (-2 * (-E z)) * H.inner z v w = _
    rw [surgeryMetric_inner, hweight]
    simp only [one_mul, sub_self, zero_mul, add_zero]
    rw [← mul_assoc, hcancel, one_mul, metricPullbackForm_apply]
  have hs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ s y :=
    (standardSurgeryHeight_contDiffAt g₀ (hne y hyU)).contMDiffAt.comp y
      (surgeryBallInclusion_contMDiff g₀ _ y)
  have heq : (fun z => -E z) =ᶠ[nhds y]
      fun z => smoothProfile (-C) q N.epsilon (s z) := by
    filter_upwards [hU.mem_nhds hyU] with z hz
    change s z < 1 at hz
    change -standardCapConformalExponent g₀ C q N.epsilon r (i z) =
      smoothProfile (-C) q N.epsilon (standardSurgeryHeight g₀ (i z))
    rw [standardCapConformalExponent_eq_on_transition g₀ C q N.epsilon hr hrA
      (by change s z ≤ 2; linarith only [hz])]
    simp only [smoothProfile, neg_mul]
  have hflat := sectionalCurvature_positiveScaling_smoothProfile_retained H D
    (fun z => -E z) hE.neg DJ s (-C) N.epsilon hq y hs heq hy a b
    hpair.1 hpair.2.1 hpair.2.2
  rw [← hflat]
  exact sectionalCurvature_eq_of_local_isometry DJ N.connection hU
    (fun z hz => (surgeryRetainedInverse_contMDiffAt g₀ N hcut (hne z hz)).contMDiffWithinAt)
    hmetric hyU a b



theorem surgeryMetric_sectional_retained_pos (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    (hpositive : ∀ x ∈ N.carrier, ∀ a b : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x a b → 0 < N.connection.sectionalCurvature x a b)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 0)
    (a b : TangentSpace (𝓡 3) y)
    (hpair : LeviCivitaData.IsOrthonormalPair
      (surgeryMetric g₀ N hcut C q eta r hlambda heta hr) y a b) :
    0 < D.sectionalCurvature y a b := by
  have hm (v w : TangentSpace (𝓡 3) y) :=
    surgeryMetric_eq_pullback_retained g₀ N hcut C q eta r hlambda heta hr hq hrA hy v w
  have hpair' : LeviCivitaData.IsOrthonormalPair g (surgeryRetainedInverse g₀ N y)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y a)
      (mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y b) := by
    unfold LeviCivitaData.IsOrthonormalPair at hpair ⊢
    simp only [metricPullbackForm_apply] at hm
    rw [← hm a a, ← hm b b, ← hm a b]
    exact hpair
  rw [surgeryMetric_sectional_retained g₀ N hcut C q eta r hlambda heta hr hq hrA D hy
    a b hpair]
  exact hpositive _ (surgeryRetainedInverse_mem g₀ N hcut y) _ _ hpair'



theorem surgeryMetric_leastSectional_retained (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 0) :
    D.leastSectionalCurvature y =
      N.connection.leastSectionalCurvature (surgeryRetainedInverse g₀ N y) := by
  let H := surgeryMetric g₀ N hcut C q eta r hlambda heta hr
  let L := mfderiv (𝓡 3) (𝓡 3) (surgeryRetainedInverse g₀ N) y
  have hm (a b : TangentSpace (𝓡 3) y) :
      H.inner y a b = g.inner (surgeryRetainedInverse g₀ N y) (L a) (L b) :=
    surgeryMetric_eq_pullback_retained g₀ N hcut C q eta r hlambda heta hr hq hrA hy a b
  have hp (a b : TangentSpace (𝓡 3) y) :
      LeviCivitaData.IsOrthonormalPair H y a b ↔
        LeviCivitaData.IsOrthonormalPair g (surgeryRetainedInverse g₀ N y) (L a) (L b) := by
    unfold LeviCivitaData.IsOrthonormalPair
    rw [hm, hm, hm]
  have hK (a b : TangentSpace (𝓡 3) y)
      (hab : LeviCivitaData.IsOrthonormalPair H y a b) :
      D.curvatureTensor y a b a b = N.connection.curvatureTensor
        (surgeryRetainedInverse g₀ N y) (L a) (L b) (L a) (L b) := by
    have hab' := (hp a b).mp hab
    have hsec := surgeryMetric_sectional_retained g₀ N hcut C q eta r
      hlambda heta hr hq hrA D hy a b hab
    dsimp only [H, L] at hab hab' ⊢
    simpa only [LeviCivitaData.sectionalCurvature, hab.1, hab.2.1, hab.2.2,
      hab'.1, hab'.2.1, hab'.2.2, one_mul, zero_pow (by decide : 2 ≠ 0),
      sub_zero, div_one] using hsec
  have hne : surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) y ≠ 0 := by
    intro hz
    rw [hz, standardSurgeryHeight_zero] at hy
    linarith [g₀.cylindrical_end.radius_pos]
  have hsurj : Function.Surjective L :=
    (surgeryRetainedInverse_mfderiv_bijective g₀ N hcut hne).2
  unfold LeviCivitaData.leastSectionalCurvature
  congr 1
  ext k
  constructor
  · rintro ⟨a, b, hab, hk⟩
    exact ⟨L a, L b, (hp a b).mp hab, hk.trans (hK a b hab)⟩
  · rintro ⟨a, b, hab, hk⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    have hab' := (hp a' b').mpr hab
    exact ⟨a', b', hab', hk.trans (hK a' b' hab').symm⟩



theorem surgeryMetric_negativeCurvaturePart_retained (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ y) ≤ 0) :
    D.negativeCurvaturePart y =
      N.connection.negativeCurvaturePart (surgeryRetainedInverse g₀ N y) := by
  unfold LeviCivitaData.negativeCurvaturePart
  rw [surgeryMetric_leastSectional_retained g₀ N hcut C q eta r hlambda heta hr hq hrA D hy]


end PoincareConjecture.M36
