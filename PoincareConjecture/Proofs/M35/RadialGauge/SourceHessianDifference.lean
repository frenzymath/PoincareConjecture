import PoincareConjecture.Proofs.M35.RadialGauge.SourceHessian
import PoincareConjecture.Proofs.M35.RadialGauge.SourceSmoothness

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "D" => V →L[ℝ] ℝ

noncomputable local instance m35SourceHessianDifferenceLocal1 :
    NormedAddCommGroup D := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35SourceHessianDifferenceLocal2 :
    NormedSpace ℝ D := ContinuousLinearMap.toNormedSpace

theorem gaugeSource_hessian_difference_norm_le
    {b : V → V} {G : V → ℝ → ℝ} {u v : V → ℝ}
    (hb : ContDiff ℝ ∞ b) (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : V) :
    ‖fderiv ℝ (fderiv ℝ (gaugeSource b G u)) x -
      fderiv ℝ (fderiv ℝ (gaugeSource b G v)) x‖ ≤
      (‖b x‖ + 2 * ‖fderiv ℝ u x‖) *
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ +
      (2 * ‖fderiv ℝ b x‖ + 2 * ‖fderiv ℝ (fderiv ℝ u) x‖ +
        2 * ‖fderiv ℝ (fderiv ℝ v) x‖ + |forcingScalarDeriv G x (u x)|) *
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ v) x‖ +
      (‖fderiv ℝ (fderiv ℝ b) x‖ + 2 * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ +
        ‖fderiv ℝ (fun y => forcingScalarDeriv G y (u y)) x‖) *
        ‖fderiv ℝ u x - fderiv ℝ v x‖ +
      ‖fderiv ℝ (fun y => forcingSpaceDeriv G y (u y) - forcingSpaceDeriv G y (v y)) x‖ +
      |forcingScalarDeriv G x (u x) - forcingScalarDeriv G x (v x)| *
        ‖fderiv ℝ (fderiv ℝ v) x‖ +
      ‖fderiv ℝ (fun y => forcingScalarDeriv G y (u y) - forcingScalarDeriv G y (v y)) x‖ *
        ‖fderiv ℝ v x‖ := by
  let p := fderiv ℝ u
  let q := fderiv ℝ v
  let H := fderiv ℝ p
  let K := fderiv ℝ q
  let db := fderiv ℝ b
  let d := fun y => p y - q y
  let e := fun y => H y - K y
  let gx := fun y => forcingSpaceDeriv G y (u y) - forcingSpaceDeriv G y (v y)
  let gz := fun y => forcingScalarDeriv G y (u y)
  let hz := fun y => forcingScalarDeriv G y (u y) - forcingScalarDeriv G y (v y)
  have hp : ContDiff ℝ ∞ p := (contDiff_infty_iff_fderiv.mp hu).2
  have hq : ContDiff ℝ ∞ q := (contDiff_infty_iff_fderiv.mp hv).2
  have hH : ContDiff ℝ ∞ H := (contDiff_infty_iff_fderiv.mp hp).2
  have hK : ContDiff ℝ ∞ K := (contDiff_infty_iff_fderiv.mp hq).2
  have hdb : ContDiff ℝ ∞ db := (contDiff_infty_iff_fderiv.mp hb).2
  have hd : ContDiff ℝ ∞ d := hp.sub hq
  have he : ContDiff ℝ ∞ e := hH.sub hK
  have hgx : ContDiff ℝ ∞ gx :=
    ((forcingSpaceDeriv_contDiff hG).comp (contDiff_id.prodMk hu)).sub
      ((forcingSpaceDeriv_contDiff hG).comp (contDiff_id.prodMk hv))
  have hgz : ContDiff ℝ ∞ gz :=
    (forcingScalarDeriv_contDiff hG).comp (contDiff_id.prodMk hu)
  have hhz : ContDiff ℝ ∞ hz := hgz.sub
    ((forcingScalarDeriv_contDiff hG).comp (contDiff_id.prodMk hv))
  have hd_eq : fderiv ℝ d x = e x :=
    ((hp.differentiable (by simp) x).hasFDerivAt.sub
      (hq.differentiable (by simp) x).hasFDerivAt).fderiv
  have he_eq : fderiv ℝ e x = fderiv ℝ H x - fderiv ℝ K x :=
    ((hH.differentiable (by simp) x).hasFDerivAt.sub
      (hK.differentiable (by simp) x).hasFDerivAt).fderiv
  have hflip : ContDiff ℝ ∞ (fun y => (e y).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).contDiff.comp he
  have hfun : (fun y => fderiv ℝ (gaugeSource b G u) y -
      fderiv ℝ (gaugeSource b G v) y) = fun y =>
      (d y).comp (db y) + (e y).flip (b y) +
      (dualSquaredDifferential (p y)).comp (e y) +
      (dualSquaredDifferential (d y)).comp (K y) + gx y + gz y • d y + hz y • q y := by
    funext y
    rw [gaugeSource_fderiv_eq_jet (hb.differentiable (by simp) y)
      (hu.differentiable (by simp) y) (hp.differentiable (by simp) y)
      (hG.differentiable (by simp) (y, u y)),
      gaugeSource_fderiv_eq_jet (hb.differentiable (by simp) y)
      (hv.differentiable (by simp) y) (hq.differentiable (by simp) y)
      (hG.differentiable (by simp) (y, v y)), sourceDerivativeJet_sub]
    simp only [d, e, gx, gz, hz, p, q, H, K, db,
      forcingSpaceDeriv, forcingScalarDeriv, add_assoc]
  have hsu := (contDiff_infty_iff_fderiv.mp (gaugeSource_contDiff hb hG hu)).2
  have hsv := (contDiff_infty_iff_fderiv.mp (gaugeSource_contDiff hb hG hv)).2
  have hdiff_eq : fderiv ℝ (fun y => fderiv ℝ (gaugeSource b G u) y -
      fderiv ℝ (gaugeSource b G v) y) x =
      fderiv ℝ (fderiv ℝ (gaugeSource b G u)) x -
        fderiv ℝ (fderiv ℝ (gaugeSource b G v)) x :=
    ((hsu.differentiable (by simp) x).hasFDerivAt.sub
      (hsv.differentiable (by simp) x).hasFDerivAt).fderiv
  rw [← hdiff_eq, hfun]
  have h1 := norm_fderiv_clm_comp_le hd hdb x
  rw [hd_eq] at h1
  have h2 := norm_fderiv_clm_apply_le hflip hb x
  rw [ContinuousLinearMap.opNorm_flip,
    norm_fderiv_flip _ (he.differentiable (by simp) x), he_eq] at h2
  have h3 := norm_fderiv_clm_comp_le (dualSquaredDifferential_contDiff hp) he x
  have h3a := mul_le_mul_of_nonneg_right (dualSquaredDifferential_norm_le (p x))
    (norm_nonneg (fderiv ℝ e x))
  have h3b := mul_le_mul_of_nonneg_right
    (norm_fderiv_dualSquaredDifferential_le (hp.differentiable (by simp) x)) (norm_nonneg (e x))
  rw [he_eq] at h3 h3a
  have h4 := norm_fderiv_clm_comp_le (dualSquaredDifferential_contDiff hd) hK x
  have h4a := mul_le_mul_of_nonneg_right (dualSquaredDifferential_norm_le (d x))
    (norm_nonneg (fderiv ℝ K x))
  have h4b := mul_le_mul_of_nonneg_right
    (norm_fderiv_dualSquaredDifferential_le (hd.differentiable (by simp) x)) (norm_nonneg (K x))
  rw [hd_eq] at h4b
  have h6 := norm_fderiv_smul_le hgz hd x
  rw [hd_eq, Real.norm_eq_abs] at h6
  have h7 := norm_fderiv_smul_le hhz hq x
  rw [Real.norm_eq_abs] at h7
  have hfirst := ((hd.clm_comp hdb).differentiable (by simp) x).hasFDerivAt
  have hsecond := ((hflip.clm_apply hb).differentiable (by simp) x).hasFDerivAt
  have hthird := (((dualSquaredDifferential_contDiff hp).clm_comp he).differentiable
    (by simp) x).hasFDerivAt
  have hfourth := (((dualSquaredDifferential_contDiff hd).clm_comp hK).differentiable
    (by simp) x).hasFDerivAt
  have hfifth := (hgx.differentiable (by simp) x).hasFDerivAt
  have hsixth := ((hgz.smul hd).differentiable (by simp) x).hasFDerivAt
  have hseventh := ((hhz.smul hq).differentiable (by simp) x).hasFDerivAt
  have hsum_eq : fderiv ℝ (fun y =>
      (d y).comp (db y) + (e y).flip (b y) +
      (dualSquaredDifferential (p y)).comp (e y) +
      (dualSquaredDifferential (d y)).comp (K y) + gx y + gz y • d y + hz y • q y) x =
      fderiv ℝ (fun y => (d y).comp (db y)) x +
      fderiv ℝ (fun y => (e y).flip (b y)) x +
      fderiv ℝ (fun y => (dualSquaredDifferential (p y)).comp (e y)) x +
      fderiv ℝ (fun y => (dualSquaredDifferential (d y)).comp (K y)) x +
      fderiv ℝ gx x + fderiv ℝ (fun y => gz y • d y) x +
      fderiv ℝ (fun y => hz y • q y) x :=
    ((((((hfirst.add hsecond).add hthird).add hfourth).add hfifth).add hsixth).add hseventh).fderiv
  rw [hsum_eq]
  have hsum := norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le h1 h2) h3) h4)
      (le_refl ‖fderiv ℝ gx x‖)) h6) h7
  change _ ≤ (‖b x‖ + 2 * ‖p x‖) * ‖fderiv ℝ H x - fderiv ℝ K x‖ +
    (2 * ‖db x‖ + 2 * ‖H x‖ + 2 * ‖K x‖ + |gz x|) * ‖e x‖ +
    (‖fderiv ℝ db x‖ + 2 * ‖fderiv ℝ K x‖ + ‖fderiv ℝ gz x‖) * ‖d x‖ +
    ‖fderiv ℝ gx x‖ + |hz x| * ‖K x‖ + ‖fderiv ℝ hz x‖ * ‖q x‖
  nlinarith only [hsum, h3a, h3b, h4a, h4b]

end PoincareConjecture.M35.RadialGauge
