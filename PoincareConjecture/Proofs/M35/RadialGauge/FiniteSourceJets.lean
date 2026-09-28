import PoincareConjecture.Proofs.M35.RadialGauge.SourceHessian
import PoincareConjecture.Proofs.M35.RadialGauge.SourceSmoothness

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {X E F W : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem norm_fderiv_bilinear_le_c1 (B : E →L[ℝ] F →L[ℝ] W)
    {f : X → E} {g : X → F} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hB : ‖B‖ ≤ 1) (x : X) :
    ‖fderiv ℝ (fun y => B (f y) (g y)) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ := by
  simpa [Finset.sum_range_succ, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]
    using B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hg x (n := 1) (by norm_num) hB

private theorem norm_fderiv_clm_comp_le_c1
    {f : X → F →L[ℝ] W} {g : X → E →L[ℝ] F}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : X) :
    ‖fderiv ℝ (fun y => (f y).comp (g y)) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ :=
  norm_fderiv_bilinear_le_c1 (ContinuousLinearMap.compL ℝ E F W) hf hg
    (ContinuousLinearMap.norm_compL_le ℝ E F W) x

private theorem norm_fderiv_clm_apply_le_c1
    {f : X → E →L[ℝ] F} {g : X → E}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : X) :
    ‖fderiv ℝ (fun y => f y (g y)) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ := by
  rw [((hf.differentiable (by norm_num) x).hasFDerivAt.clm_apply
    (hg.differentiable (by norm_num) x).hasFDerivAt).fderiv]
  exact (norm_add_le _ _).trans (add_le_add ((f x).opNorm_comp_le _)
    (by simpa only [ContinuousLinearMap.opNorm_flip] using
      (fderiv ℝ f x).flip.le_opNorm (g x)))

private theorem norm_fderiv_smul_le_c1 {f : X → ℝ} {g : X → F}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : X) :
    ‖fderiv ℝ (fun y => f y • g y) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ :=
  norm_fderiv_bilinear_le_c1 (ContinuousLinearMap.lsmul ℝ ℝ) hf hg
    ContinuousLinearMap.opNorm_lsmul_le x

private theorem forcing_graph_fderiv_bound
    {A : X → ℝ → F} {u : X → ℝ} {x : X} {eta M : ℝ}
    (hM : 0 ≤ M)
    (hA : DifferentiableAt ℝ (fun p : X × ℝ => A p.1 p.2) (x, u x))
    (hu : DifferentiableAt ℝ u x)
    (hDA : ‖fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, u x)‖ ≤ M)
    (hp : ‖fderiv ℝ u x‖ ≤ eta) :
    ‖fderiv ℝ (fun y => A y (u y)) x‖ ≤ M * (1 + eta) := by
  let q := fderiv ℝ (fun p : X × ℝ => A p.1 p.2) (x, u x)
  have hspace : ‖q.comp (ContinuousLinearMap.inl ℝ X ℝ)‖ ≤ M :=
    (q.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inl_le_one ℝ X ℝ) (norm_nonneg q)).trans (by simpa using hDA))
  have hscalar : ‖q (0, 1)‖ ≤ M := by
    have h := q.le_opNorm (0, 1)
    simpa only [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one, mul_one]
      using h.trans (by simpa using hDA)
  have heq : fderiv ℝ (fun y => A y (u y)) x =
      q.comp ((ContinuousLinearMap.id ℝ X).prod (fderiv ℝ u x)) := by
    simpa only [Function.comp_def, id_eq, q] using
      (hA.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hu.hasFDerivAt)).fderiv
  rw [heq]
  have hg := graph_derivative_norm_le_general q (fderiv ℝ u x)
  have hm := mul_le_mul hscalar hp (norm_nonneg _) hM
  nlinarith only [hg, hspace, hm]

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "D" => V →L[ℝ] ℝ

noncomputable local instance m35FiniteSourceJetsLocal1 :
    NormedAddCommGroup D := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35FiniteSourceJetsLocal2 :
    NormedSpace ℝ D := ContinuousLinearMap.toNormedSpace

theorem gaugeSource_contDiff_two_of_three {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ}
    (hb : ContDiff ℝ 2 b) (hG : ContDiff ℝ 2 (fun p : V × ℝ => G p.1 p.2))
    (hu : ContDiff ℝ 3 u) : ContDiff ℝ 2 (gaugeSource b G u) := by
  have hp : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hsquare : ContDiff ℝ 2 (fun x => ‖fderiv ℝ u x‖ ^ 2) := by
    simp_rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_dual]
    apply ContDiff.sum
    intro i _
    exact (hp.clm_apply contDiff_const).pow 2
  exact ((hp.clm_apply hb).add hsquare).add
    (hG.comp (contDiff_id.prodMk (hu.of_le (by norm_num))))

theorem gaugeSource_hessian_norm_le_of_contDiff_three
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ}
    (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hu : ContDiff ℝ 3 u) (x : V) :
    ‖fderiv ℝ (fderiv ℝ (gaugeSource b G u)) x‖ ≤
      (‖b x‖ + 2 * ‖fderiv ℝ u x‖) *
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ +
      (2 * ‖fderiv ℝ b x‖ + 2 * ‖fderiv ℝ (fderiv ℝ u) x‖ +
        |forcingScalarDeriv G x (u x)|) * ‖fderiv ℝ (fderiv ℝ u) x‖ +
      ‖fderiv ℝ u x‖ * ‖fderiv ℝ (fderiv ℝ b) x‖ +
      ‖fderiv ℝ (fun y => forcingSpaceDeriv G y (u y)) x‖ +
      ‖fderiv ℝ (fun y => forcingScalarDeriv G y (u y)) x‖ * ‖fderiv ℝ u x‖ := by
  let p := fderiv ℝ u
  let H := fderiv ℝ p
  let db := fderiv ℝ b
  let gx := fun y => forcingSpaceDeriv G y (u y)
  let gz := fun y => forcingScalarDeriv G y (u y)
  have hp2 : ContDiff ℝ 2 p := hu.fderiv_right (by norm_num)
  have hp : ContDiff ℝ 1 p := hp2.of_le (by norm_num)
  have hH : ContDiff ℝ 1 H := hp2.fderiv_right (by norm_num)
  have hdb : ContDiff ℝ 1 db := ((contDiff_infty_iff_fderiv.mp hb).2).of_le (by simp)
  have hflip : ContDiff ℝ 1 (fun y => (H y).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).contDiff.comp hH
  have hgx : ContDiff ℝ 1 gx := ((forcingSpaceDeriv_contDiff hG).of_le (by simp)).comp
    (contDiff_id.prodMk (hu.of_le (by norm_num)))
  have hgz : ContDiff ℝ 1 gz := ((forcingScalarDeriv_contDiff hG).of_le (by simp)).comp
    (contDiff_id.prodMk (hu.of_le (by norm_num)))
  have hsq : ContDiff ℝ 1 (fun y => dualSquaredDifferential (p y)) :=
    dualSquaredLinear.contDiff.comp hp
  have heq : fderiv ℝ (gaugeSource b G u) = fun y =>
      (p y).comp (db y) + (H y).flip (b y) +
        (dualSquaredDifferential (p y)).comp (H y) + gx y + gz y • p y := by
    funext y
    exact gaugeSource_fderiv_eq_jet (hb.differentiable (by simp) y)
      (hu.differentiable (by norm_num) y) (hp.differentiable (by norm_num) y)
      (hG.differentiable (by simp) (y, u y))
  rw [heq]
  have h1 := norm_fderiv_clm_comp_le_c1 hp hdb x
  have h2 := norm_fderiv_clm_apply_le_c1 hflip (hb.of_le (by simp)) x
  rw [ContinuousLinearMap.opNorm_flip, norm_fderiv_flip _ (hH.differentiable (by norm_num) x)] at h2
  have h3 := norm_fderiv_clm_comp_le_c1 hsq hH x
  have h3a := mul_le_mul_of_nonneg_right (dualSquaredDifferential_norm_le (p x))
    (norm_nonneg (fderiv ℝ H x))
  have h3b := mul_le_mul_of_nonneg_right
    (norm_fderiv_dualSquaredDifferential_le (hp.differentiable (by norm_num) x)) (norm_nonneg (H x))
  have h5 := norm_fderiv_smul_le_c1 hgz hp x
  have hfirst := (hp.clm_comp hdb).differentiable (by norm_num) x
  have hsecond := (hflip.clm_apply (hb.of_le (by simp))).differentiable (by norm_num) x
  have hthird := (hsq.clm_comp hH).differentiable (by norm_num) x
  have hfourth := hgx.differentiable (by norm_num) x
  have hfifth := (hgz.smul hp).differentiable (by norm_num) x
  have hsum_eq : fderiv ℝ (fun y => (p y).comp (db y) + (H y).flip (b y) +
      (dualSquaredDifferential (p y)).comp (H y) + gx y + gz y • p y) x =
        fderiv ℝ (fun y => (p y).comp (db y)) x +
        fderiv ℝ (fun y => (H y).flip (b y)) x +
        fderiv ℝ (fun y => (dualSquaredDifferential (p y)).comp (H y)) x +
        fderiv ℝ gx x + fderiv ℝ (fun y => gz y • p y) x :=
    ((((hfirst.hasFDerivAt.add hsecond.hasFDerivAt).add hthird.hasFDerivAt).add
      hfourth.hasFDerivAt).add hfifth.hasFDerivAt).fderiv
  rw [hsum_eq]
  have hs := norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le h1 h2) h3)
      (le_refl ‖fderiv ℝ gx x‖)) h5
  change _ ≤ (‖b x‖ + 2 * ‖p x‖) * ‖fderiv ℝ H x‖ +
    (2 * ‖db x‖ + 2 * ‖H x‖ + |gz x|) * ‖H x‖ +
    ‖p x‖ * ‖fderiv ℝ db x‖ + ‖fderiv ℝ gx x‖ + ‖fderiv ℝ gz x‖ * ‖p x‖
  rw [Real.norm_eq_abs] at h5 hs
  nlinarith only [hs, h3a, h3b]

theorem gaugeSource_hessian_bound_of_contDiff_three
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ} {x : V}
    {eta B B1 B2 L1 M2 H J : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1)
    (hL1 : 0 ≤ L1) (hM2 : 0 ≤ M2) (hH : 0 ≤ H)
    (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hu : ContDiff ℝ 3 u)
    (hbb : ‖b x‖ ≤ B) (hdb : ‖fderiv ℝ b x‖ ≤ B1)
    (hddb : ‖fderiv ℝ (fderiv ℝ b) x‖ ≤ B2)
    (hGz : |forcingScalarDeriv G x (u x)| ≤ L1)
    (hDGx : ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, u x)‖ ≤ M2)
    (hDGz : ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2) (x, u x)‖ ≤ M2)
    (hp : ‖fderiv ℝ u x‖ ≤ eta)
    (hh : ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H)
    (hj : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ J) :
    ‖fderiv ℝ (fderiv ℝ (gaugeSource b G u)) x‖ ≤
      (B + 2 * eta) * J + (2 * B1 + 2 * H + L1) * H + eta * B2 + M2 * (1 + eta) ^ 2 := by
  have hgx := forcing_graph_fderiv_bound hM2
    ((forcingSpaceDeriv_contDiff hG).differentiable (by simp) (x, u x))
    (hu.differentiable (by norm_num) x) hDGx hp
  have hgz := forcing_graph_fderiv_bound hM2
    ((forcingScalarDeriv_contDiff hG).differentiable (by simp) (x, u x))
    (hu.differentiable (by norm_num) x) hDGz hp
  have hs := gaugeSource_hessian_norm_le_of_contDiff_three hb hG hu x
  have h1 := mul_le_mul (add_le_add hbb
    (mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num))) hj
    (ContinuousLinearMap.opNorm_nonneg _) (show 0 ≤ B + 2 * eta by positivity)
  have h2 := mul_le_mul
    (show 2 * ‖fderiv ℝ b x‖ + 2 * ‖fderiv ℝ (fderiv ℝ u) x‖ +
        |forcingScalarDeriv G x (u x)| ≤ 2 * B1 + 2 * H + L1 by linarith only [hdb, hh, hGz])
    hh (norm_nonneg _) (show 0 ≤ 2 * B1 + 2 * H + L1 by positivity)
  have h3 := mul_le_mul hp hddb (ContinuousLinearMap.opNorm_nonneg _) heta
  have h4 := mul_le_mul hgz hp (norm_nonneg _) (show 0 ≤ M2 * (1 + eta) by positivity)
  nlinarith only [hs, h1, h2, h3, h4, hgx]

end PoincareConjecture.M35.RadialGauge
