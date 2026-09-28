import PoincareConjecture.Proofs.M35.RadialGauge.JetCalculus

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "D" => V →L[ℝ] ℝ

noncomputable local instance m35SourceHessianLocal1 :
    NormedAddCommGroup D := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35SourceHessianLocal2 :
    NormedSpace ℝ D := ContinuousLinearMap.toNormedSpace

theorem gaugeSource_hessian_norm_le
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ}
    (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hu : ContDiff ℝ ∞ u) (x : V) :
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
  have hp : ContDiff ℝ ∞ p := (contDiff_infty_iff_fderiv.mp hu).2
  have hH : ContDiff ℝ ∞ H := (contDiff_infty_iff_fderiv.mp hp).2
  have hdb : ContDiff ℝ ∞ db := (contDiff_infty_iff_fderiv.mp hb).2
  have hflip : ContDiff ℝ ∞ (fun y => (H y).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).contDiff.comp hH
  have hgx : ContDiff ℝ ∞ gx := (forcingSpaceDeriv_contDiff hG).comp (contDiff_id.prodMk hu)
  have hgz : ContDiff ℝ ∞ gz := (forcingScalarDeriv_contDiff hG).comp (contDiff_id.prodMk hu)
  have heq : fderiv ℝ (gaugeSource b G u) = fun y =>
      (p y).comp (db y) + (H y).flip (b y) +
        (dualSquaredDifferential (p y)).comp (H y) + gx y + gz y • p y := by
    funext y
    exact gaugeSource_fderiv_eq_jet (hb.differentiable (by simp) y)
      (hu.differentiable (by simp) y) (hp.differentiable (by simp) y)
      (hG.differentiable (by simp) (y, u y))
  rw [heq]
  have h1 := norm_fderiv_clm_comp_le hp hdb x
  have h2 := norm_fderiv_clm_apply_le hflip hb x
  rw [ContinuousLinearMap.opNorm_flip, norm_fderiv_flip _ (hH.differentiable (by simp) x)] at h2
  have h3 := norm_fderiv_clm_comp_le (dualSquaredDifferential_contDiff hp) hH x
  have h3a := mul_le_mul_of_nonneg_right (dualSquaredDifferential_norm_le (p x))
    (norm_nonneg (fderiv ℝ H x))
  have h3b := mul_le_mul_of_nonneg_right
    (norm_fderiv_dualSquaredDifferential_le (hp.differentiable (by simp) x)) (norm_nonneg (H x))
  have h5 := norm_fderiv_smul_le hgz hp x
  have hfirst := (hp.clm_comp hdb).differentiable (by simp) x
  have hsecond := (hflip.clm_apply hb).differentiable (by simp) x
  have hthird := ((dualSquaredDifferential_contDiff hp).clm_comp hH).differentiable (by simp) x
  have hfourth := hgx.differentiable (by simp) x
  have hfifth := (hgz.smul hp).differentiable (by simp) x
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
  nlinarith

theorem forcing_graph_fderiv_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : V → ℝ → F} {u : V → ℝ} {x : V}
    (hA : DifferentiableAt ℝ (fun p : V × ℝ => A p.1 p.2) (x, u x))
    (hu : DifferentiableAt ℝ u x) :
    ‖fderiv ℝ (fun y => A y (u y)) x‖ ≤
      ‖(fderiv ℝ (fun p : V × ℝ => A p.1 p.2) (x, u x)).comp
        (ContinuousLinearMap.inl ℝ V ℝ)‖ +
      ‖fderiv ℝ (fun p : V × ℝ => A p.1 p.2) (x, u x) (0, 1)‖ * ‖fderiv ℝ u x‖ := by
  have ha := hA.hasFDerivAt
  have hg := (hasFDerivAt_id x).prodMk hu.hasFDerivAt
  have hh := ha.comp x hg
  have heq : fderiv ℝ (fun y => A y (u y)) x =
      (fderiv ℝ (fun p : V × ℝ => A p.1 p.2) (x, u x)).comp
        ((ContinuousLinearMap.id ℝ V).prod (fderiv ℝ u x)) :=
    hh.fderiv
  rw [heq]
  exact graph_derivative_norm_le_general _ _

theorem gaugeSource_weighted_hessian_bound
    {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ} {x : V}
    {eta B B1 B2 L1 M2 C2 H J : ℝ}
    (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hL1 : 0 ≤ L1) (hM2 : 0 ≤ M2) (hH : 0 ≤ H)
    (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hu : ContDiff ℝ ∞ u)
    (hbb : ‖b x‖ ≤ B) (hdb : ‖fderiv ℝ b x‖ ≤ B1)
    (hddb : ‖fderiv ℝ (fderiv ℝ b) x‖ ≤ B2)
    (hGz : |forcingScalarDeriv G x (u x)| ≤ L1)
    (hGxx : (1 + ‖x‖) *
      ‖(fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2) (x, u x)).comp
        (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ C2)
    (hGxz : ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv G p.1 p.2)
      (x, u x) (0, 1)‖ ≤ M2)
    (hGzx : ‖(fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2)
      (x, u x)).comp (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ M2)
    (hGzz : ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv G p.1 p.2)
      (x, u x) (0, 1)‖ ≤ M2)
    (hp : (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ eta)
    (hh : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H)
    (hj : (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ J) :
    (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugeSource b G u)) x‖ ≤
      (B + 2 * eta) * J + (2 * B1 + 2 * H + L1) * H +
        (B2 + 2 * M2 + M2 * eta) * eta + C2 := by
  have hw : 0 ≤ 1 + ‖x‖ := by positivity
  have hpn : ‖fderiv ℝ u x‖ ≤ eta := by
    nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ u x))]
  have hhn : ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ H := by
    nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ (fderiv ℝ u) x))]
  have hgx := forcing_graph_fderiv_norm_le (A := forcingSpaceDeriv G) (u := u)
    ((forcingSpaceDeriv_contDiff hG).differentiable (by simp) (x, u x))
    (hu.differentiable (by simp) x)
  have hgz := forcing_graph_fderiv_norm_le (A := forcingScalarDeriv G) (u := u)
    ((forcingScalarDeriv_contDiff hG).differentiable (by simp) (x, u x))
    (hu.differentiable (by simp) x)
  have hgx' : (1 + ‖x‖) * ‖fderiv ℝ (fun y => forcingSpaceDeriv G y (u y)) x‖ ≤
      C2 + M2 * eta := by
    have h1 := mul_le_mul_of_nonneg_left hgx hw
    have h2 := mul_le_mul_of_nonneg_right hGxz
      (mul_nonneg hw (norm_nonneg (fderiv ℝ u x)))
    have h3 := mul_le_mul_of_nonneg_left hp hM2
    nlinarith
  have hgz' : ‖fderiv ℝ (fun y => forcingScalarDeriv G y (u y)) x‖ ≤
      M2 + M2 * eta := by
    have h1 := mul_le_mul hGzz hpn (norm_nonneg _) hM2
    linarith
  have hmain := mul_le_mul_of_nonneg_left (gaugeSource_hessian_norm_le hb hG hu x) hw
  have hhigh := mul_le_mul_of_nonneg_left hj (show 0 ≤ B + 2 * eta by positivity)
  have hhigh' := mul_le_mul_of_nonneg_right
    (add_le_add hbb (mul_le_mul_of_nonneg_left hpn (show (0 : ℝ) ≤ 2 by norm_num)))
    (mul_nonneg hw (norm_nonneg (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x)))
  have hhess := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * B1 + 2 * H + L1 by positivity)
  have hhess' := mul_le_mul_of_nonneg_right
    (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hdb (show (0 : ℝ) ≤ 2 by norm_num))
      (mul_le_mul_of_nonneg_left hhn (show (0 : ℝ) ≤ 2 by norm_num))) hGz)
    (mul_nonneg hw (norm_nonneg (fderiv ℝ (fderiv ℝ u) x)))
  have hp1 := mul_le_mul_of_nonneg_left hp hB2
  have hp1' := mul_le_mul_of_nonneg_right hddb (mul_nonneg hw (norm_nonneg (fderiv ℝ u x)))
  have hp2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ M2 + M2 * eta by positivity)
  have hp2' := mul_le_mul_of_nonneg_right hgz' (mul_nonneg hw (norm_nonneg (fderiv ℝ u x)))
  nlinarith only [hmain, hhigh, hhigh', hhess, hhess', hp1, hp1', hp2, hp2', hgx']

end PoincareConjecture.M35.RadialGauge
